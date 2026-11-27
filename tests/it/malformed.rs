// Copyright 2023 Datafuse Labs.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Regression tests for malformed JSONB bytes, deep nesting, and oversized headers.
//!
//! Every public API must return an error (or a documented fallback) for such
//! input instead of panicking, overflowing the stack, or allocating memory
//! proportional to a length field instead of the input size.

use std::panic::{self, AssertUnwindSafe};

use jsonb::jsonpath::parse_json_path;
use jsonb::keypath::parse_key_paths;
use jsonb::*;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::util::{nested_arrays, with_big_stack, within_timeout};

/// Nesting limit for arrays and objects (`MAX_NESTING_DEPTH` in the crate).
const MAX_DEPTH: usize = 512;

/// Builds `{"k":{"k":...{}...}}` with `depth` objects, using the public builder.
fn nested_objects(depth: usize) -> OwnedJsonb {
    let mut cur = "{}".parse::<OwnedJsonb>().unwrap();
    for _ in 1..depth {
        cur = OwnedJsonb::build_object([("k", cur.as_raw())]).unwrap();
    }
    cur
}

fn jsonb(words: &[u32], tail: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = words.iter().flat_map(|w| w.to_be_bytes()).collect();
    out.extend_from_slice(tail);
    out
}

#[test]
fn malformed_number_payloads_return_errors() {
    let mut cases = vec![
        (
            "empty number".to_string(),
            jsonb(&[0x2000_0000, 0x2000_0000], &[]),
            Some(Error::InvalidJsonbNumber),
        ),
        (
            "float with 1 byte".to_string(),
            jsonb(&[0x2000_0000, 0x2000_0002], &[0x60, 0xf9]),
            Some(Error::InvalidJsonbNumber),
        ),
        (
            "truncated payload".to_string(),
            jsonb(&[0x2000_0000, 0x2000_0001], &[]),
            None,
        ),
    ];
    // Zero, NaN and the infinities are one tag byte. Bytes after it were
    // ignored, so one value had many encodings.
    for tag in [0x00, 0x10, 0x20, 0x30] {
        let exact = jsonb(&[0x2000_0000, 0x2000_0001], &[tag]);
        assert!(RawJsonb::new(&exact).to_value().is_ok(), "{tag:#x}");
        cases.push((
            format!("tag {tag:#x} with a payload"),
            jsonb(&[0x2000_0000, 0x2000_0002], &[tag, 0xff]),
            Some(Error::InvalidJsonbNumber),
        ));
    }
    for (name, bytes, error) in &cases {
        let raw = RawJsonb::new(bytes);
        assert!(raw.as_number().is_err(), "{name}: as_number");
        let to_value = raw.to_value().err();
        assert!(to_value.is_some(), "{name}: to_value");
        if error.is_some() {
            assert_eq!(&to_value, error, "{name}: to_value");
            assert_eq!(&raw.as_number().err(), error, "{name}: as_number");
        }
        assert!(
            from_raw_jsonb::<i64>(&raw).is_err(),
            "{name}: from_raw_jsonb"
        );
        assert!(serde_json::to_string(&raw).is_err(), "{name}: serialize");
        assert!(from_slice(bytes).is_err(), "{name}: from_slice");
        // `to_string` falls back to treating the bytes as text.
        assert_eq!(raw.to_string(), String::from_utf8_lossy(bytes), "{name}");
    }
}

#[test]
fn malformed_extension_payloads_return_errors() {
    let mut cases = vec![
        (
            "empty extension".to_string(),
            jsonb(&[0x2000_0000, 0x6000_0000], &[]),
            Some(Error::InvalidJsonbExtension),
        ),
        (
            "truncated extension".to_string(),
            jsonb(&[0x2000_0000, 0x6000_008f], &[]),
            None,
        ),
    ];
    // Dates, timestamps, timestamps with a time zone and intervals of the
    // wrong length reported `InvalidJsonbNumber`.
    for tag in [0x10, 0x20, 0x30, 0x40] {
        cases.push((
            format!("extension {tag:#x} of the wrong length"),
            jsonb(&[0x2000_0000, 0x6000_0002], &[tag, 0]),
            Some(Error::InvalidJsonbExtension),
        ));
    }
    for (name, bytes, error) in &cases {
        let raw = RawJsonb::new(bytes);
        let as_extension = raw.as_extension_value().err();
        let to_value = raw.to_value().err();
        assert!(as_extension.is_some(), "{name}: as_extension_value");
        assert!(to_value.is_some(), "{name}: to_value");
        if error.is_some() {
            assert_eq!(&as_extension, error, "{name}: as_extension_value");
            assert_eq!(&to_value, error, "{name}: to_value");
        }
        assert!(
            from_raw_jsonb::<String>(&raw).is_err(),
            "{name}: from_raw_jsonb"
        );
        assert!(serde_json::to_string(&raw).is_err(), "{name}: serialize");
    }
}

#[test]
fn truncated_container_payloads_return_errors() {
    // An array whose container element claims more bytes than remain.
    let bytes = jsonb(&[0x8000_0001, 0x5000_0010], &[0x80, 0, 0, 0]);
    let raw = RawJsonb::new(&bytes);
    assert!(serde_json::to_string(&raw).is_err());
    assert!(raw.to_value().is_err());
}

#[test]
fn unknown_jentry_type_returns_error_instead_of_panicking() {
    // Type code 0x7 is not assigned to any JSONB value kind.
    let bytes = jsonb(&[0x8000_0001, 0x7000_0000], &[]);
    let raw = RawJsonb::new(&bytes);
    assert_eq!(raw.array_values().err(), Some(Error::InvalidJsonb));
    assert_eq!(raw.get_by_index(0).err(), Some(Error::InvalidJsonb));
}

#[test]
fn null_and_boolean_entries_with_a_length_are_rejected() {
    // Null and booleans have no payload, and every encoder writes them with
    // length 0. Readers used to disagree on such entries: on the array, some
    // skipped the 2 bytes and read `[true,"cd"]`, `from_slice` ignored them and
    // read `[true,"ab"]`, and `from_raw_jsonb` failed. On the scalar, whose
    // payload lies beyond the data, some failed and others returned `true`.
    let cases = [
        (
            "array element in range",
            jsonb(&[0x8000_0002, 0x4000_0002, 0x1000_0002], b"abcd"),
        ),
        (
            "scalar out of range",
            jsonb(&[0x2000_0000, 0x4000_0005], &[]),
        ),
        ("scalar null", jsonb(&[0x2000_0000, 0x0000_0001], b"x")),
        ("scalar false", jsonb(&[0x2000_0000, 0x3000_0001], b"x")),
        (
            "object value",
            jsonb(&[0x4000_0001, 0x1000_0001, 0x0000_0001], b"kx"),
        ),
    ];
    for (name, bytes) in &cases {
        let raw = RawJsonb::new(bytes);
        assert_eq!(
            raw.to_value().err(),
            Some(Error::InvalidJsonbJEntry),
            "{name}: to_value"
        );
        assert!(from_slice(bytes).is_err(), "{name}: from_slice");
        assert!(
            from_raw_jsonb::<serde_json::Value>(&raw).is_err(),
            "{name}: from_raw_jsonb"
        );
        assert!(serde_json::to_string(&raw).is_err(), "{name}: serialize");
        assert_eq!(raw.to_pretty_string(), "null", "{name}: to_pretty_string");
        assert_eq!(
            raw.contains(&raw).err(),
            Some(Error::InvalidJsonbJEntry),
            "{name}: contains"
        );
        // `convert_to_comparable` returns no bytes when it fails.
        assert!(raw.convert_to_comparable().is_empty(), "{name}: comparable");
    }

    // The same values with length 0 are valid.
    let valid = jsonb(&[0x8000_0002, 0x4000_0000, 0x1000_0002], b"ab");
    assert_eq!(
        RawJsonb::new(&valid).to_value().unwrap().to_string(),
        r#"[true,"ab"]"#
    );
}

/// Wraps `1` in `count` scalar headers, each holding a container entry for the next.
fn scalar_wrapped(count: usize) -> Vec<u8> {
    let inner = Value::Number(Number::UInt64(1)).to_vec().unwrap();
    let mut out = Vec::with_capacity(count * 8 + inner.len());
    for i in 0..count {
        let len = (count - i - 1) * 8 + inner.len();
        out.extend_from_slice(&jsonb(&[0x2000_0000, 0x5000_0000 | len as u32], &[]));
    }
    out.extend_from_slice(&inner);
    out
}

#[test]
fn container_entries_under_scalar_headers_are_rejected() {
    // A scalar header holds one scalar; no encoder puts a container entry
    // under it. Such wrappers used to be unwrapped without counting depth, so
    // 1,000,000 of them (8 MB) overflowed the stack in `to_value` and
    // `from_slice` despite the nesting limit.
    let one = scalar_wrapped(1);
    let raw = RawJsonb::new(&one);
    assert_eq!(raw.to_value().err(), Some(Error::InvalidJsonb));
    assert!(from_raw_jsonb::<serde_json::Value>(&raw).is_err());
    // The typed paths reported `UnexpectedType`, as if it were a valid
    // container.
    assert_eq!(from_raw_jsonb::<String>(&raw), Err(Error::InvalidJsonb));
    assert_eq!(from_raw_jsonb::<u64>(&raw), Err(Error::InvalidJsonb));
    assert_eq!(from_raw_jsonb::<bool>(&raw), Err(Error::InvalidJsonb));
    assert_eq!(from_raw_jsonb::<()>(&raw), Err(Error::InvalidJsonb));
    assert!(serde_json::to_string(&raw).is_err());
    assert!(raw.jsonb_item_type().is_err());
    // `from_slice` falls back to parsing the bytes as JSON text, which fails.
    assert!(from_slice(&one).is_err());

    // Each API fails at the first wrapper, so this runs on the default test
    // stack; before the fix it overflowed even a 64 MiB stack.
    let deep = scalar_wrapped(1_000_000);
    let raw = RawJsonb::new(&deep);
    assert_eq!(raw.to_value().err(), Some(Error::InvalidJsonb));
    assert!(from_slice(&deep).is_err());
    assert!(from_raw_jsonb::<serde_json::Value>(&raw).is_err());
    assert!(serde_json::to_string(&raw).is_err());
}

#[test]
fn display_does_not_panic_on_out_of_range_values() {
    let values = [
        Value::Date(Date { value: i32::MAX }),
        Value::Date(Date { value: i32::MIN }),
        Value::TimestampTz(TimestampTz {
            offset: i32::MAX,
            value: 0,
        }),
        Value::TimestampTz(TimestampTz {
            offset: i32::MIN,
            value: i64::MIN,
        }),
        Value::Interval(Interval {
            months: i32::MIN,
            days: i32::MIN,
            micros: i64::MIN,
        }),
        Value::TimestampNtz(TimestampNtz { value: i64::MAX }),
        Value::TimestampNtz(TimestampNtz { value: i64::MIN }),
    ];
    for value in &values {
        let mut buf = Vec::new();
        value.write_to_vec(&mut buf).unwrap();
        let raw = RawJsonb::new(&buf);
        assert!(!raw.to_string().is_empty(), "{value:?}");
        assert!(from_raw_jsonb::<String>(&raw).is_ok(), "{value:?}");
    }
    let interval = Interval {
        months: 0,
        days: i32::MIN,
        micros: i64::MIN,
    };
    assert_eq!(
        interval.to_string(),
        "-2147483648 days -2562047788:00:54.775808"
    );
}

/// Encodes `depth` nested arrays directly, in linear time, for very deep inputs.
fn deep_arrays_bytes(depth: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(depth * 8);
    for level in 0..depth - 1 {
        // The child container has `depth - level - 2` containers below it.
        let child_len = 8 * (depth - level - 2) + 4;
        out.extend_from_slice(&0x8000_0001_u32.to_be_bytes());
        out.extend_from_slice(&(0x5000_0000_u32 | child_len as u32).to_be_bytes());
    }
    out.extend_from_slice(&0x8000_0000_u32.to_be_bytes());
    out
}

#[test]
fn text_parsers_enforce_nesting_limit() {
    with_big_stack(|| {
        for (open, empty, close) in [("[", "[]", "]"), (r#"{"a":"#, "{}", "}")] {
            let text = |depth: usize| {
                let outer = depth - 1;
                format!("{}{empty}{}", open.repeat(outer), close.repeat(outer))
            };
            let ok = text(MAX_DEPTH);
            assert!(parse_value(ok.as_bytes()).is_ok());
            assert!(ParseOptions::new()
                .standard_mode(true)
                .parse_value(ok.as_bytes())
                .is_ok());
            assert!(parse_owned_jsonb(ok.as_bytes()).is_ok());
            for depth in [MAX_DEPTH + 1, 100_000] {
                let deep = text(depth);
                let err = Some(Error::RecursionLimitExceeded);
                assert_eq!(parse_value(deep.as_bytes()).err(), err, "{open} x {depth}");
                assert_eq!(
                    ParseOptions::new()
                        .standard_mode(true)
                        .parse_value(deep.as_bytes())
                        .err(),
                    err
                );
                assert_eq!(parse_owned_jsonb(deep.as_bytes()).err(), err);
                assert_eq!(deep.parse::<OwnedJsonb>().err(), err);
            }
        }
    });
}

/// Runs every recursive read API on `raw` and reports whether each succeeded.
fn recursive_api_results(raw: RawJsonb<'_>) -> Vec<(&'static str, bool)> {
    let all = parse_json_path(b"$.**").unwrap();
    vec![
        ("to_value", raw.to_value().is_ok()),
        (
            "to_string",
            matches!(raw.to_string().chars().next(), Some('[' | '{')),
        ),
        ("to_pretty_string", raw.to_pretty_string() != "null"),
        ("serde_json::to_string", serde_json::to_string(&raw).is_ok()),
        ("from_slice", from_slice(raw.as_ref()).is_ok()),
        (
            "from_raw_jsonb",
            from_raw_jsonb::<serde_json::Value>(&raw).is_ok(),
        ),
        ("partial_cmp", raw.partial_cmp(&raw).is_some()),
        ("contains", raw.contains(&raw).is_ok()),
        ("strip_nulls", raw.strip_nulls().is_ok()),
        (
            "convert_to_comparable",
            !raw.convert_to_comparable().is_empty(),
        ),
        ("select_by_path", raw.select_by_path(&all).is_ok()),
        ("jaq", jaq_json::Val::try_from(raw).is_ok()),
        (
            "visit_scalar_key_paths",
            raw.visit_scalar_key_paths(false, |_| Ok(())).is_ok(),
        ),
    ]
}

#[test]
fn binary_apis_enforce_nesting_limit() {
    /// Checks that every recursive read API rejects `bytes`, and that the
    /// decoders report the nesting limit.
    fn assert_rejected(bytes: &[u8], what: &str) {
        let raw = RawJsonb::new(bytes);
        for (api, passed) in recursive_api_results(raw) {
            assert!(!passed, "{api} should reject {what}");
        }
        assert_eq!(
            raw.to_value().err(),
            Some(Error::RecursionLimitExceeded),
            "{what}"
        );
        // `from_slice` used to parse the bytes again as JSON text and report
        // a syntax error.
        assert_eq!(
            from_slice(bytes).err(),
            Some(Error::RecursionLimitExceeded),
            "from_slice of {what}"
        );
    }

    with_big_stack(|| {
        for (shape, build) in [
            ("arrays", nested_arrays as fn(usize) -> OwnedJsonb),
            ("objects", nested_objects),
        ] {
            let ok = build(MAX_DEPTH);
            for (api, passed) in recursive_api_results(ok.as_raw()) {
                assert!(passed, "{api} should accept {MAX_DEPTH} nested {shape}");
            }
            // The JSON text writers match serde_json at the limit too.
            let raw = ok.as_raw();
            assert_eq!(raw.to_string(), serde_json::to_string(&raw).unwrap());
            assert_eq!(
                raw.to_pretty_string(),
                serde_json::to_string_pretty(&raw).unwrap()
            );
            let deep = build(MAX_DEPTH + 1);
            assert_rejected(deep.as_ref(), &format!("{} nested {shape}", MAX_DEPTH + 1));
        }
        assert_eq!(deep_arrays_bytes(5), nested_arrays(5).to_vec());
        // The builder rejects this depth, so the bytes are written directly.
        // Without the limit, 100000 levels need far more than the 64 MiB stack.
        assert_rejected(&deep_arrays_bytes(100_000), "100000 nested arrays");
    });
}

#[test]
fn oversized_container_headers_are_rejected_early() {
    // Each header declares 2^29 - 1 entries but no JEntries follow.
    for header in [0x9FFF_FFFF_u32, 0x5FFF_FFFF] {
        let bytes = header.to_be_bytes();
        let raw = RawJsonb::new(&bytes);
        assert_eq!(raw.to_value().err(), Some(Error::InvalidEOF), "{header:#x}");
        assert!(raw.array_length().is_err(), "{header:#x}");
        assert!(raw.object_keys().is_err(), "{header:#x}");
        assert!(
            from_raw_jsonb::<serde_json::Value>(&raw).is_err(),
            "{header:#x}"
        );
        assert!(serde_json::to_value(raw).is_err(), "{header:#x}");
        assert!(from_slice(&bytes).is_err(), "{header:#x}");
    }
}

fn mutation_corpus() -> Vec<Vec<u8>> {
    let texts = [
        "null",
        "true",
        "-7",
        "123456",
        "-1.5",
        "1e300",
        "123456789012345678901234567890.5",
        r#""测试""#,
        r#"[1,"a",null,{"k":[true,2.5]}]"#,
        r#"{"a":{"b":[1,2,{"c":"d"}]},"e":3.25,"f":null}"#,
        r#"[[[[["x"]]]],{"y":{"z":[]}}]"#,
    ];
    let mut corpus: Vec<Vec<u8>> = texts
        .iter()
        .map(|t| t.parse::<OwnedJsonb>().unwrap().to_vec())
        .collect();
    for value in [
        Value::Date(Date { value: 19000 }),
        Value::TimestampTz(TimestampTz {
            offset: 3600,
            value: 1,
        }),
        Value::Interval(Interval {
            months: 1,
            days: 2,
            micros: 3,
        }),
        Value::TimestampNtz(TimestampNtz { value: -1 }),
        Value::Array(vec![Value::Binary(b"z"), Value::Date(Date { value: 1 })]),
    ] {
        let mut buf = Vec::new();
        value.write_to_vec(&mut buf).unwrap();
        corpus.push(buf);
    }
    corpus
}

/// Applies a few random byte edits, biased towards JEntry/header words.
fn mutate(rng: &mut SmallRng, seed: &[u8]) -> Vec<u8> {
    const WORDS: [u32; 8] = [
        0x2000_0000,
        0x6000_0000,
        0x7000_0000,
        0x5000_0004,
        0x1000_0000,
        0x2000_0001,
        0x8000_0002,
        0x9FFF_FFFF,
    ];
    let mut v = seed.to_vec();
    for _ in 0..rng.random_range(1..4) {
        let n = v.len().max(1);
        match rng.random_range(0..5) {
            0 if !v.is_empty() => {
                let i = rng.random_range(0..v.len());
                v[i] = rng.random();
            }
            1 => v.truncate(rng.random_range(0..n)),
            2 => {
                let i = rng.random_range(0..=v.len());
                v.insert(i, rng.random());
            }
            3 if v.len() >= 4 => {
                let i = rng.random_range(0..=(v.len() - 4)) & !3;
                let w = WORDS[rng.random_range(0..WORDS.len())];
                v[i..i + 4].copy_from_slice(&w.to_be_bytes());
            }
            _ => {}
        }
    }
    v
}

#[test]
fn mutated_jsonb_never_panics() {
    let corpus = mutation_corpus();
    let other = r#"[1,{"a":"b"}]"#.parse::<OwnedJsonb>().unwrap();
    let other = other.as_raw();
    let keys = ["a", "k"].into_iter().collect();
    let path = parse_json_path(b"$.a[*].b").unwrap();
    let mut rng = SmallRng::seed_from_u64(0x5eed);
    for _ in 0..3000 {
        let seed = &corpus[rng.random_range(0..corpus.len())];
        let bytes = mutate(&mut rng, seed);
        let raw = RawJsonb::new(&bytes);
        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = from_slice(&bytes);
            let _ = raw.to_value();
            let _ = raw.to_string();
            let _ = raw.to_pretty_string();
            let _ = from_raw_jsonb::<serde_json::Value>(&raw);
            let _ = from_raw_jsonb::<String>(&raw);
            let _ = from_raw_jsonb::<f64>(&raw);
            let _ = raw.type_of();
            let _ = raw.to_str();
            let _ = raw.as_number();
            let _ = raw.as_extension_value();
            let _ = raw.array_values();
            let _ = raw.array_distinct();
            let _ = raw.array_intersection(&other);
            let _ = raw.array_overlap(&other);
            let _ = raw.object_each();
            let _ = raw.object_keys();
            let _ = raw.object_pick(&keys);
            let _ = raw.get_by_index(1);
            let _ = raw.get_by_name("a", true);
            let _ = raw.strip_nulls();
            let _ = raw.concat(&other);
            let _ = raw.contains(&other);
            let _ = other.contains(&raw);
            let _ = raw.convert_to_comparable();
            let _ = raw.partial_cmp(&other);
            let _ = raw.select_by_path(&path);
            let _ = OwnedJsonb::build_array([raw, other]).map(|o| o.to_string());
        }));
        assert!(result.is_ok(), "panicked on input {bytes:02x?}");
    }
}

#[test]
fn encoding_rejects_strings_that_overflow_the_length_field() {
    // JEntry lengths have 28 bits, so a 256 MiB string cannot be encoded.
    let big = String::from_utf8(vec![b'a'; 1 << 28]).unwrap();
    let value = Value::String(big.as_str().into());
    assert_eq!(value.to_vec().err(), Some(Error::ValueTooLarge));

    // A failed `write_to_vec` leaves earlier buffer contents untouched.
    let mut buf = b"prefix".to_vec();
    let nested = Value::Array(vec![Value::Null, value]);
    assert_eq!(nested.write_to_vec(&mut buf), Err(Error::ValueTooLarge));
    assert_eq!(buf, b"prefix");

    let raw = RawJsonb::new(b"\x20\0\0\0\0\0\0\0");
    assert_eq!(
        OwnedJsonb::build_object([(big.as_str(), raw)]).err(),
        Some(Error::ValueTooLarge)
    );
    assert_eq!(to_owned_jsonb(&big).err(), Some(Error::ValueTooLarge));

    // One byte below the limit still round-trips.
    let fits = &big[..(1 << 28) - 1];
    let encoded = Value::String(fits.into()).to_vec().unwrap();
    assert_eq!(
        RawJsonb::new(&encoded).as_str().unwrap().unwrap().len(),
        fits.len()
    );
}

#[test]
fn comparable_encoding_orders_values_past_255_levels() {
    with_big_stack(|| {
        // `a` = [X, 3] and `b` = [Y], where X and Y are 256 nested arrays whose
        // innermost arrays are `[]` and `[2]`. `a < b` because `[]` < `[2]`.
        // A `u8` depth wrapped 257 to 1, so the old encoding compared `3`
        // against `2` and ordered `a > b`.
        let nest = |inner: &str| format!("{}{inner}{}", "[".repeat(255), "]".repeat(255));
        let a = format!("[{},3]", nest("[]")).parse::<OwnedJsonb>().unwrap();
        let b = format!("[{}]", nest("[2]")).parse::<OwnedJsonb>().unwrap();
        assert_eq!(
            a.as_raw().partial_cmp(&b.as_raw()),
            Some(std::cmp::Ordering::Less)
        );
        assert!(a.as_raw().convert_to_comparable() < b.as_raw().convert_to_comparable());
    });
}

#[test]
fn ignored_values_are_skipped_and_checked() {
    use serde::de::IgnoredAny;
    use serde::Deserialize;

    #[derive(Debug, Deserialize, PartialEq)]
    struct Partial {
        b: String,
    }

    // Unknown fields `a` and `c`, including nested containers, are skipped.
    let object = r#"{"a":[1,{"x":2}],"b":"y","c":null}"#.parse::<OwnedJsonb>().unwrap();
    let partial: Partial = from_raw_jsonb(&object.as_raw()).unwrap();
    assert_eq!(partial, Partial { b: "y".to_string() });

    // Array elements are read in order, so skipping one must advance past it.
    let array = r#"[[1,[2]],"z",{"k":"v"},3]"#.parse::<OwnedJsonb>().unwrap();
    let (_, second, _, fourth): (IgnoredAny, String, IgnoredAny, u8) =
        from_raw_jsonb(&array.as_raw()).unwrap();
    assert_eq!((second.as_str(), fourth), ("z", 3));

    // A whole value can be ignored too.
    assert!(from_raw_jsonb::<IgnoredAny>(&array.as_raw()).is_ok());

    // Ignoring a value used to skip its bytes unread. At the top level that
    // accepted any input, even an empty one.
    for bytes in [
        &b""[..],
        b"\x01",
        b"\xff\xff\xff\xff",
        b"\x20\0\0\0\x70\0\0\0",
    ] {
        assert!(
            from_raw_jsonb::<IgnoredAny>(&RawJsonb::new(bytes)).is_err(),
            "{bytes:02x?}"
        );
    }

    // `{"a": <invalid UTF-8 string>, "b": "y"}`: the unknown field `a` is
    // checked although it is skipped.
    let bytes = jsonb(
        &[
            0x4000_0002,
            0x1000_0001,
            0x1000_0001,
            0x1000_0001,
            0x1000_0001,
        ],
        b"ab\xffy",
    );
    let err = from_raw_jsonb::<Partial>(&RawJsonb::new(&bytes)).unwrap_err();
    assert_eq!(err, Error::InvalidUtf8);

    // Ignored values count toward the nesting limit.
    with_big_stack(|| {
        let ok = nested_arrays(MAX_DEPTH);
        assert!(from_raw_jsonb::<IgnoredAny>(&ok.as_raw()).is_ok());
        let deep = nested_arrays(MAX_DEPTH + 1);
        assert_eq!(
            from_raw_jsonb::<IgnoredAny>(&deep.as_raw()).err(),
            Some(Error::RecursionLimitExceeded)
        );
    });
}

#[test]
fn iterators_stop_after_an_error() {
    // An array of 2 whose second element claims 65535 bytes that are not there
    // (found by fuzzing). Iterators used to return the same error forever, so
    // `nth(n)` looped `n` times.
    let bytes = jsonb(&[0x8000_0002, 0x2000_0002, 0x1000_ffff], &[0x50, 0x01]);
    let result = within_timeout("get_by_index(usize::MAX)", move || {
        RawJsonb::new(&bytes)
            .get_by_index(usize::MAX)
            .map(|v| v.is_some())
    });
    assert_eq!(result, Ok(false));

    let bytes = jsonb(&[0x8000_0002, 0x2000_0002, 0x1000_ffff], &[0x50, 0x01]);
    let result = within_timeout("get_by_index(1)", move || {
        RawJsonb::new(&bytes).get_by_index(1).map(|v| v.is_some())
    });
    assert_eq!(result, Err(Error::InvalidJsonb));

    // The same corruption inside `{"k": <array>}`, reached through a key path.
    let array = jsonb(&[0x8000_0002, 0x2000_0002, 0x1000_ffff], &[0x50, 0x01]);
    let mut bytes = jsonb(
        &[0x4000_0001, 0x1000_0001, 0x5000_0000 | array.len() as u32],
        b"k",
    );
    bytes.extend_from_slice(&array);
    let path = parse_key_paths(b"{k,1}").unwrap().to_owned();
    let result = within_timeout("get_by_keypath", move || {
        let path = path.as_key_paths();
        RawJsonb::new(&bytes)
            .get_by_keypath(path.paths.iter())
            .map(|v| v.is_some())
    });
    assert!(result.is_err(), "{result:?}");

    // `[<invalid UTF-8 string>, null]`. Reaching index 1 reads index 0, which
    // fails; the iterator then stopped and `nth(1)` returned `None`, so these
    // returned `Ok(None)` and `delete_by_keypath` deleted nothing (found in
    // review).
    let bytes = jsonb(&[0x8000_0002, 0x1000_0001, 0x0000_0000], &[0xff]);
    let raw = RawJsonb::new(&bytes);
    for index in [0, 1] {
        assert_eq!(
            raw.get_by_index(index).err(),
            Some(Error::InvalidUtf8),
            "get_by_index({index})"
        );
    }
    // Indices past the end return at once without reading any element.
    for index in [2, usize::MAX] {
        assert_eq!(raw.get_by_index(index), Ok(None), "get_by_index({index})");
    }
    for path in ["{0}", "{1}", "{-1}"] {
        let path = parse_key_paths(path.as_bytes()).unwrap();
        assert_eq!(
            raw.get_by_keypath(path.paths.iter()).err(),
            Some(Error::InvalidUtf8),
            "get_by_keypath({path})"
        );
        assert_eq!(
            raw.delete_by_keypath(path.paths.iter()).err(),
            Some(Error::InvalidUtf8),
            "delete_by_keypath({path})"
        );
    }
    let path = parse_key_paths(b"{2}").unwrap();
    assert_eq!(raw.get_by_keypath(path.paths.iter()), Ok(None));
}

#[test]
fn non_string_object_keys_are_rejected() {
    use std::collections::HashMap;
    // Each key is valid as its own type, so only its type marks the object
    // as invalid. `to_value` and serialization rejected such keys, but the
    // object functions, key lookup, `$.*`, comparison and typed
    // deserialization read them: the null key matched and compared equal to
    // "", and a map with integer keys read the number key as 1.
    let cases = [
        (
            "null key",
            jsonb(&[0x4000_0001, 0x0000_0000, 0x1000_0001], b"v"),
            "",
        ),
        (
            "number key",
            jsonb(&[0x4000_0001, 0x2000_0002, 0x1000_0001], b"\x50\x01v"),
            "\u{50}\u{1}",
        ),
        (
            "extension key",
            jsonb(&[0x4000_0001, 0x6000_0001, 0x1000_0001], b"kv"),
            "k",
        ),
    ];
    let one: OwnedJsonb = "1".parse().unwrap();
    let keys: std::collections::BTreeSet<&str> = ["k"].into_iter().collect();
    let all_values = parse_json_path(b"$.*").unwrap();
    let empty_key = jsonb(&[0x4000_0001, 0x1000_0000, 0x1000_0001], b"v");
    let invalid = Some(Error::InvalidJsonb);
    for (name, bytes, key) in &cases {
        let raw = RawJsonb::new(bytes);
        assert_eq!(raw.to_value().err(), invalid, "{name}: to_value");
        assert!(from_slice(bytes).is_err(), "{name}: from_slice");
        assert!(serde_json::to_string(&raw).is_err(), "{name}: serialize");
        assert!(jaq_json::Val::try_from(raw).is_err(), "{name}: jaq");
        assert_eq!(raw.object_keys().err(), invalid, "{name}: object_keys");
        assert_eq!(raw.object_each().err(), invalid, "{name}: object_each");
        assert_eq!(
            raw.object_insert("x", &one.as_raw(), false).err(),
            invalid,
            "{name}: object_insert"
        );
        assert_eq!(
            raw.object_delete(&keys).err(),
            invalid,
            "{name}: object_delete"
        );
        assert_eq!(raw.object_pick(&keys).err(), invalid, "{name}: object_pick");
        assert_eq!(
            raw.get_by_name(key, false).err(),
            invalid,
            "{name}: get_by_name"
        );
        assert_eq!(
            raw.select_by_path(&all_values).err(),
            invalid,
            "{name}: $.*"
        );
        assert_eq!(
            raw.partial_cmp(&RawJsonb::new(&empty_key)),
            None,
            "{name}: partial_cmp"
        );
        assert_eq!(
            from_raw_jsonb::<HashMap<u8, String>>(&raw).err(),
            invalid,
            "{name}: from_raw_jsonb"
        );
    }

    // The same object with a string key still works.
    let bytes = jsonb(&[0x4000_0001, 0x1000_0001, 0x1000_0001], b"kv");
    let raw = RawJsonb::new(&bytes);
    let each = raw.object_each().unwrap().unwrap();
    assert_eq!(each.len(), 1);
    assert_eq!(each[0].0, "k");
    assert_eq!(each[0].1.to_string(), r#""v""#);
    assert_eq!(raw.object_pick(&keys).unwrap().to_string(), r#"{"k":"v"}"#);
    assert_eq!(
        raw.get_by_name("k", false).unwrap().unwrap().to_string(),
        r#""v""#
    );
    assert_eq!(raw.object_keys().unwrap().unwrap().to_string(), r#"["k"]"#);
}

#[test]
fn building_from_a_scalar_copies_only_its_payload() {
    // The string "a" followed by a stray byte "b". Readers ignore bytes past
    // the payload, but the builder copied them too, so the next member's
    // payload started one byte late and read as "bc".
    let trailing = jsonb(&[0x2000_0000, 0x1000_0001], b"ab");
    let cd: OwnedJsonb = r#""cd""#.parse().unwrap();
    let array = OwnedJsonb::build_array([RawJsonb::new(&trailing), cd.as_raw()]).unwrap();
    assert_eq!(array.to_string(), r#"["a","cd"]"#);
    let object =
        OwnedJsonb::build_object([("x", RawJsonb::new(&trailing)), ("y", cd.as_raw())]).unwrap();
    assert_eq!(object.to_string(), r#"{"x":"a","y":"cd"}"#);

    // A truncated payload, and a container entry under a scalar header, are
    // invalid; they used to be copied as they were.
    let truncated = jsonb(&[0x2000_0000, 0x1000_0005], b"ab");
    assert!(OwnedJsonb::build_array([RawJsonb::new(&truncated)]).is_err());
    let wrapped = scalar_wrapped(1);
    assert_eq!(
        OwnedJsonb::build_array([RawJsonb::new(&wrapped)]).err(),
        Some(Error::InvalidJsonb)
    );
}

#[test]
fn deserializing_a_member_reads_nothing_past_its_payload() {
    // An array holding one string, whose `JEntry` length covers the array's
    // header and `JEntry` but not the string's one byte.
    let inner = [0x8000_0001_u32, 0x1000_0001];
    let inner: Vec<u8> = inner.iter().flat_map(|w| w.to_be_bytes()).collect();

    // `[<inner>, "x"]`. Reading the inner array checked its payloads against
    // the whole document, not against the member, so the inner string read
    // the next member's "x" and this read as `[["x"], "x"]`.
    let array = jsonb(
        &[0x8000_0002, 0x5000_0008, 0x1000_0001],
        &[&inner[..], b"x"].concat(),
    );
    let raw = RawJsonb::new(&array);
    assert!(raw.to_value().is_err());
    assert_eq!(
        from_raw_jsonb::<(Vec<String>, String)>(&raw),
        Err(Error::InvalidEOF)
    );
    assert_eq!(
        from_raw_jsonb::<serde_json::Value>(&raw),
        Err(Error::InvalidEOF)
    );

    // `{"a": <inner>, "b": "x"}` read as `{"a": ["x"], "b": "x"}`.
    let object = jsonb(
        &[
            0x4000_0002,
            0x1000_0001,
            0x1000_0001,
            0x5000_0008,
            0x1000_0001,
        ],
        &[&b"ab"[..], &inner, b"x"].concat(),
    );
    let raw = RawJsonb::new(&object);
    assert!(raw.to_value().is_err());
    assert_eq!(
        from_raw_jsonb::<serde_json::Value>(&raw),
        Err(Error::InvalidEOF)
    );

    // `[{"V": <inner>} + "x"]`: the object's own length includes a stray
    // "x" after its value, which the variant's value read as its string.
    #[derive(Debug, serde::Deserialize)]
    #[allow(dead_code)]
    enum Variant {
        V(Vec<String>),
    }
    let enum_object = jsonb(
        &[0x4000_0001, 0x1000_0001, 0x5000_0008],
        &[&b"V"[..], &inner, b"x"].concat(),
    );
    let array = jsonb(
        &[0x8000_0001, 0x5000_0000 | enum_object.len() as u32],
        &enum_object,
    );
    let raw = RawJsonb::new(&array);
    assert!(raw.to_value().is_err());
    assert_eq!(
        from_raw_jsonb::<Vec<Variant>>(&raw).err(),
        Some(Error::InvalidEOF)
    );

    // `[<scalar header without its JEntry>, "@\0\0\0"]`: a container member
    // four bytes long, holding only a scalar header. Its `JEntry` was read
    // from the next member, whose bytes `0x40000000` are a `true` `JEntry`,
    // so this read as `[true, "@\0\0\0"]`.
    let bytes = jsonb(
        &[0x8000_0002, 0x5000_0004, 0x1000_0004, 0x2000_0000],
        b"@\0\0\0",
    );
    let raw = RawJsonb::new(&bytes);
    assert!(raw.to_value().is_err());
    assert_eq!(
        from_raw_jsonb::<serde_json::Value>(&raw),
        Err(Error::InvalidEOF)
    );
}
