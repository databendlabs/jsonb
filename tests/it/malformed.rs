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

use ethnum::I256;
use jsonb::jsonpath::parse_json_path;
use jsonb::keypath::parse_key_paths;
use jsonb::*;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

/// Nesting limit for arrays and objects (`MAX_NESTING_DEPTH` in the crate).
const MAX_DEPTH: usize = 512;
/// Parenthesis nesting limit for JSONPath (`MAX_JSON_PATH_DEPTH` in the crate).
const MAX_PATH_DEPTH: usize = 64;
/// `&&` and `||` limit for JSONPath (`MAX_JSON_PATH_LOGICAL_OPERATORS` in the crate).
const MAX_PATH_LOGICAL_OPERATORS: usize = 256;

/// Runs `f` on a thread with a large stack.
///
/// Debug builds use up to ~9 KiB of stack per nesting level, so walking
/// `MAX_DEPTH` levels needs more than the test harness's default 2 MiB.
fn with_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// Builds `[[...[]...]]` with `depth` arrays, using the public builder.
fn nested_arrays(depth: usize) -> OwnedJsonb {
    let mut cur = "[]".parse::<OwnedJsonb>().unwrap();
    for _ in 1..depth {
        cur = OwnedJsonb::build_array([cur.as_raw()]).unwrap();
    }
    cur
}

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
    let cases = [
        ("empty number", jsonb(&[0x2000_0000, 0x2000_0000], &[])),
        (
            "float with 1 byte",
            jsonb(&[0x2000_0000, 0x2000_0002], &[0x60, 0xf9]),
        ),
        ("truncated payload", jsonb(&[0x2000_0000, 0x2000_0001], &[])),
    ];
    for (name, bytes) in &cases {
        let raw = RawJsonb::new(bytes);
        assert!(raw.as_number().is_err(), "{name}: as_number");
        assert!(raw.to_value().is_err(), "{name}: to_value");
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
    let cases = [
        ("empty extension", jsonb(&[0x2000_0000, 0x6000_0000], &[])),
        (
            "truncated extension",
            jsonb(&[0x2000_0000, 0x6000_008f], &[]),
        ),
    ];
    for (name, bytes) in &cases {
        let raw = RawJsonb::new(bytes);
        assert!(
            raw.as_extension_value().is_err(),
            "{name}: as_extension_value"
        );
        assert!(raw.to_value().is_err(), "{name}: to_value");
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
fn from_slice_rejects_non_string_object_key() {
    // `{null: "v"}`
    let bytes = jsonb(&[0x4000_0001, 0x0000_0000, 0x1000_0001], b"v");
    assert!(from_slice(&bytes).is_err());
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

#[test]
fn decimal_display_handles_any_scale_and_value() {
    // 2^255 - 1 and 2^255, as literals so the test does not depend on `ethnum`'s Display.
    let i256_max = "57896044618658097711785492504343953926634992332820282019728792003956564819967";
    let i256_min_abs =
        "57896044618658097711785492504343953926634992332820282019728792003956564819968";
    let (int, frac) = i256_min_abs.split_at(i256_min_abs.len() - 3);
    let cases = vec![
        (
            Number::Decimal128(Decimal128 {
                scale: 2,
                value: 12345,
            }),
            "123.45".to_string(),
        ),
        (
            Number::Decimal128(Decimal128 {
                scale: 40,
                value: 5,
            }),
            format!("0.{}5", "0".repeat(39)),
        ),
        (
            Number::Decimal128(Decimal128 {
                scale: 0,
                value: i128::MIN,
            }),
            i128::MIN.to_string(),
        ),
        (
            Number::Decimal128(Decimal128 {
                scale: 39,
                value: i128::MIN,
            }),
            "-0.170141183460469231731687303715884105728".to_string(),
        ),
        (
            Number::Decimal64(Decimal64 {
                scale: 200,
                value: -1,
            }),
            format!("-0.{}1", "0".repeat(199)),
        ),
        (
            Number::Decimal256(Decimal256 {
                scale: 0,
                value: I256::MAX,
            }),
            i256_max.to_string(),
        ),
        (
            Number::Decimal256(Decimal256 {
                scale: 3,
                value: I256::MIN,
            }),
            format!("-{int}.{frac}"),
        ),
        (
            // Below the fast path's 10^76 bound, but a scale beyond 76 digits;
            // the low 10^38 chunk needs zero padding.
            Number::Decimal256(Decimal256 {
                scale: 80,
                value: I256::from(10_i128.pow(37)) * I256::from(70_i128) + I256::from(42_i128),
            }),
            format!("0.{}7{}42", "0".repeat(41), "0".repeat(36)),
        ),
    ];
    for (number, expected) in &cases {
        assert_eq!(&number.to_string(), expected, "{number:?}");
    }
}

#[test]
fn decimal_comparison_with_huge_scale_difference_does_not_panic() {
    let small = Number::Decimal128(Decimal128 { scale: 0, value: 1 });
    let tiny = Number::Decimal128(Decimal128 {
        scale: 200,
        value: 1,
    });
    assert_eq!(small.partial_cmp(&tiny), Some(std::cmp::Ordering::Greater));
    let small = Number::Decimal256(Decimal256 {
        scale: 0,
        value: I256::ONE,
    });
    let tiny = Number::Decimal256(Decimal256 {
        scale: 200,
        value: I256::ONE,
    });
    assert_eq!(tiny.partial_cmp(&small), Some(std::cmp::Ordering::Less));
}

#[test]
fn json_path_rejects_unterminated_string() {
    for path in [r#"""#, r#""a"#, r#"$."a"#, r#"$["a"#] {
        assert!(parse_json_path(path.as_bytes()).is_err(), "{path}");
        assert!(parse_key_paths(path.as_bytes()).is_err(), "{path}");
    }
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
fn deep_arrays_bytes_matches_builder() {
    assert_eq!(deep_arrays_bytes(5), nested_arrays(5).to_vec());
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
            assert!(parse_value_standard_mode(ok.as_bytes()).is_ok());
            assert!(parse_owned_jsonb(ok.as_bytes()).is_ok());
            for depth in [MAX_DEPTH + 1, 100_000] {
                let deep = text(depth);
                let err = Some(Error::RecursionLimitExceeded);
                assert_eq!(parse_value(deep.as_bytes()).err(), err, "{open} x {depth}");
                assert_eq!(parse_value_standard_mode(deep.as_bytes()).err(), err);
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
    with_big_stack(|| {
        for (shape, build) in [
            ("arrays", nested_arrays as fn(usize) -> OwnedJsonb),
            ("objects", nested_objects),
        ] {
            let ok = build(MAX_DEPTH);
            for (api, passed) in recursive_api_results(ok.as_raw()) {
                assert!(passed, "{api} should accept {MAX_DEPTH} nested {shape}");
            }
            let deep = build(MAX_DEPTH + 1);
            for (api, passed) in recursive_api_results(deep.as_raw()) {
                assert!(
                    !passed,
                    "{api} should reject {} nested {shape}",
                    MAX_DEPTH + 1
                );
            }
            assert_eq!(
                deep.as_raw().to_value().err(),
                Some(Error::RecursionLimitExceeded)
            );
        }
    });
}

#[test]
fn binary_apis_reject_very_deep_input() {
    // Without the limit, 100000 levels need far more than the 64 MiB test stack.
    with_big_stack(|| {
        let bytes = deep_arrays_bytes(100_000);
        for (api, passed) in recursive_api_results(RawJsonb::new(&bytes)) {
            assert!(!passed, "{api} should reject 100000 nested arrays");
        }
    });
}

#[test]
fn json_path_enforces_paren_limit() {
    let path = |depth: usize| {
        let inner = depth - 1;
        format!("$ ? ({}@ == 1{})", "(".repeat(inner), ")".repeat(inner))
    };
    with_big_stack(move || {
        assert!(parse_json_path(path(MAX_PATH_DEPTH).as_bytes()).is_ok());
    });
    for depth in [MAX_PATH_DEPTH + 1, 100_000] {
        assert_eq!(
            parse_json_path(path(depth).as_bytes()).err(),
            Some(Error::RecursionLimitExceeded),
            "depth {depth}"
        );
    }
    // Parentheses inside string literals do not count.
    let quoted = format!(r#"$ ? (@ == "{}")"#, "(".repeat(1000));
    assert!(parse_json_path(quoted.as_bytes()).is_ok());
}

#[test]
fn json_path_enforces_logical_operator_limit() {
    // `&&` and `||` chains parse without recursion but build a left-nested
    // tree as deep as the chain, which formatting, evaluation, cloning,
    // comparison and dropping walk recursively. 100000 operators used to
    // overflow the stack in all of them (found in review).
    let filter = |operators: usize, op: &str| {
        let operands = vec!["@ == 0"; operators + 1];
        format!("$ ? ({})", operands.join(&format!(" {op} ")))
    };
    let doc: OwnedJsonb = "[0,1]".parse().unwrap();
    // The limit runs on the test thread's default stack, without `with_big_stack`.
    for op in ["||", "&&"] {
        let text = filter(MAX_PATH_LOGICAL_OPERATORS, op);
        let path = parse_json_path(text.as_bytes()).unwrap();
        let formatted = path.to_string();
        assert_eq!(parse_json_path(formatted.as_bytes()).unwrap(), path.clone());
        assert_eq!(doc.as_raw().select_by_path(&path).unwrap().len(), 1);
        for operators in [MAX_PATH_LOGICAL_OPERATORS + 1, 100_000] {
            assert_eq!(
                parse_json_path(filter(operators, op).as_bytes()).err(),
                Some(Error::RecursionLimitExceeded),
                "{operators} {op}"
            );
        }
    }
    // The limit counts operators across the whole path, including root
    // expressions and nested filters.
    let root = vec!["$[0] == 0"; MAX_PATH_LOGICAL_OPERATORS + 2].join(" || ");
    assert!(parse_json_path(root.as_bytes()).is_err());
    let half = vec!["@ == 0"; MAX_PATH_LOGICAL_OPERATORS / 2 + 1].join(" || ");
    let nested = format!("$ ? (exists(@ ? ({half})) || {half})");
    assert!(parse_json_path(nested.as_bytes()).is_err());
    // Operators inside string literals do not count.
    let quoted = format!(r#"$ ? (@ == "{}")"#, "||&&".repeat(1000));
    assert!(parse_json_path(quoted.as_bytes()).is_ok());
}

#[test]
fn json_path_logical_operator_limit_counts_only_operators() {
    // `&` does not end an unquoted field name, so `a&&a` is one name. The
    // limit used to be counted by scanning the text, which rejected names
    // with more than 256 `&&`, and broke `Display` round-trips of quoted ones
    // because `Display` writes them unquoted (found in review).
    let doc: OwnedJsonb = r#"{"a&&a": 1}"#.parse().unwrap();
    let path = parse_json_path(b"$.a&&a").unwrap();
    assert_eq!(doc.as_raw().select_by_path(&path).unwrap().len(), 1);
    let name = format!("{}a", "a&&".repeat(1000));
    for text in [format!("$.{name}"), format!(r#"$."{name}""#)] {
        let path = parse_json_path(text.as_bytes()).unwrap();
        let formatted = path.to_string();
        assert_eq!(parse_json_path(formatted.as_bytes()).unwrap(), path);
    }

    // Each form has exactly `k` operators. The parser backtracks over some of
    // them, for example trying a root expression before a plain path, so a
    // chain can be parsed more than once; each operator must count once.
    fn chain(k: usize, op: &str) -> String {
        vec!["@ == 0"; k + 1].join(&format!(" {op} "))
    }
    /// A name and a function that writes the form with `k` operators.
    type Form = (&'static str, fn(usize) -> String);
    let forms: [Form; 8] = [
        ("filter with ||", |k| format!("$ ? ({})", chain(k, "||"))),
        ("filter with &&", |k| format!("$ ? ({})", chain(k, "&&"))),
        ("filter after a step", |k| {
            format!("$.a ? ({})", chain(k, "||"))
        }),
        ("filter on items", |k| {
            format!("$.a[*] ? ({})", chain(k, "&&"))
        }),
        ("root expression", |k| {
            vec!["$.a[0] == 0"; k + 1].join(" || ")
        }),
        ("mixed && and ||", |k| {
            let mut text = String::from("$ ? (@ == 0");
            for i in 0..k {
                text.push_str(if i % 2 == 0 {
                    " && @ == 0"
                } else {
                    " || @ == 0"
                });
            }
            text + ")"
        }),
        ("split by parentheses", |k| {
            let left = k / 2;
            let right = k - left - 1;
            format!("$ ? (({}) && ({}))", chain(left, "||"), chain(right, "||"))
        }),
        ("split by a nested filter", |k| {
            let inner = k / 2;
            let outer = k - inner - 1;
            format!(
                "$ ? (exists(@ ? ({})) || {})",
                chain(inner, "||"),
                chain(outer, "||")
            )
        }),
    ];
    let doc: OwnedJsonb = r#"{"a": [0, 1]}"#.parse().unwrap();
    for (form, path) in forms {
        let text = path(MAX_PATH_LOGICAL_OPERATORS);
        let parsed = parse_json_path(text.as_bytes()).unwrap_or_else(|e| panic!("{form}: {e:?}"));
        let formatted = parsed.to_string();
        assert_eq!(
            parse_json_path(formatted.as_bytes()).as_ref(),
            Ok(&parsed),
            "{form}: round-trip"
        );
        assert!(doc.as_raw().select_by_path(&parsed).is_ok(), "{form}");
        assert_eq!(
            parse_json_path(path(MAX_PATH_LOGICAL_OPERATORS + 1).as_bytes()).err(),
            Some(Error::RecursionLimitExceeded),
            "{form}"
        );
    }
}

#[test]
fn recursive_descent_reaches_levels_beyond_255() {
    with_big_stack(|| {
        // Levels are `u8`, so an open `to last` range is the only way to match
        // past level 255; the innermost `[]` of 300 nested arrays is level 299.
        let deep = nested_arrays(300);
        let path = parse_json_path(b"$.**{255 to last}").unwrap();
        let selected = deep.as_raw().select_by_path(&path).unwrap();
        assert_eq!(selected.len(), 300 - 255);
        assert_eq!(selected.last().unwrap().to_string(), "[]");
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
fn deserializing_skips_unknown_fields_and_ignored_elements() {
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
}

#[test]
fn signed_indexes_do_not_overflow() {
    let array = "[1,2,3]".parse::<OwnedJsonb>().unwrap();
    let raw = array.as_raw();
    assert_eq!(
        raw.delete_by_index(i32::MIN).unwrap().to_string(),
        "[1,2,3]"
    );
    assert_eq!(raw.delete_by_index(-1).unwrap().to_string(), "[1,2]");
    let one = "1".parse::<OwnedJsonb>().unwrap();
    assert_eq!(
        raw.array_insert(i32::MIN, &one.as_raw())
            .unwrap()
            .to_string(),
        "[1,1,2,3]"
    );
    assert_eq!(
        raw.array_insert(i32::MAX, &one.as_raw())
            .unwrap()
            .to_string(),
        "[1,2,3,1]"
    );
    for path in [
        "$[last + 2147483647]",
        "$[last - 2147483647]",
        "$[-2147483648]",
    ] {
        let path = parse_json_path(path.as_bytes()).unwrap();
        assert!(raw.select_by_path(&path).unwrap().is_empty());
    }
}

#[test]
fn json_path_slices_outside_the_array_select_nothing() {
    // These used to loop over `0..=usize::MAX` after an end index underflowed.
    let array = "[1,2]".parse::<OwnedJsonb>().unwrap();
    let empty = "[]".parse::<OwnedJsonb>().unwrap();
    for (doc, path) in [
        (&array, "$[0 to last - 5]"),
        (&empty, "$[0 to 3]"),
        (&array, "$[5 to 9]"),
    ] {
        let path = parse_json_path(path.as_bytes()).unwrap();
        assert!(doc.as_raw().select_by_path(&path).unwrap().is_empty());
    }
    let path = parse_json_path(b"$[1 to 9]").unwrap();
    let selected = array.as_raw().select_by_path(&path).unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].to_string(), "2");
}

#[test]
fn path_display_round_trips_special_names() {
    // Names that need quoting or escaping when shown. The parsers reject empty
    // quoted names, so `""` is not included.
    for name in [r#"st"ore"#, "a b", "a.b", "a\\b", "$x", "1st", "tab\there"] {
        let quoted = serde_json::to_string(name).unwrap();
        for text in [
            format!("$.{quoted}"),
            format!("$[{quoted}]"),
            format!("$:{quoted}"),
            format!("a:{quoted}"),
        ] {
            let path = parse_json_path(text.as_bytes()).unwrap();
            let shown = path.to_string();
            assert_eq!(
                parse_json_path(shown.as_bytes()).unwrap(),
                path,
                "{text} shown as {shown}"
            );
        }
        let text = format!("{{{quoted},0}}");
        let key_paths = parse_key_paths(text.as_bytes()).unwrap();
        let shown = key_paths.to_string();
        assert_eq!(
            parse_key_paths(shown.as_bytes()).unwrap(),
            key_paths,
            "{text} shown as {shown}"
        );
    }
}

/// Runs `f` on its own thread and fails if it does not finish within 10 seconds.
fn within_timeout<T: Send + 'static>(name: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || tx.send(f()).unwrap());
    rx.recv_timeout(std::time::Duration::from_secs(10))
        .unwrap_or_else(|_| panic!("{name} did not finish within 10 seconds"))
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
}

#[test]
fn indexing_reports_errors_in_skipped_elements() {
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
fn json_path_evaluation_is_bounded() {
    // Chained `.**` steps produce about C(depth + k - 1, k) items: 4 steps on
    // 100 nested arrays select 4.4 million, the fuzzer's 90 steps far more.
    let nested: OwnedJsonb = format!("{}{}", "[".repeat(100), "]".repeat(100))
        .parse()
        .unwrap();
    let fuzzed = "$.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.* .**.**.**.**.**.**.**.**.**.**.**.* .**.**.**.**.**.**.**.**.**.**.*[1].**[1]";
    for (doc, path) in [
        (nested.clone(), "$.**.**.**.**".to_string()),
        (nested.clone(), fuzzed.to_string()),
        (r#"{"a":[[[1]]]}"#.parse().unwrap(), fuzzed.to_string()),
    ] {
        let result = within_timeout(&path.clone(), move || {
            let path = parse_json_path(path.as_bytes()).unwrap();
            let raw = doc.as_raw();
            [
                raw.select_by_path(&path).map(|_| ()),
                raw.select_array_by_path(&path).map(|_| ()),
                raw.select_first_by_path(&path).map(|_| ()),
                raw.select_value_by_path(&path).map(|_| ()),
                raw.path_exists(&path).map(|_| ()),
            ]
        });
        for r in result {
            assert_eq!(r, Err(Error::JsonPathTooComplex));
        }
    }

    // Comparisons check every pair until one matches. No pair matches here,
    // so 2000 x 2000 values is 4 million comparisons.
    let list =
        |range: std::ops::Range<i32>| range.map(|i| i.to_string()).collect::<Vec<_>>().join(",");
    let values: OwnedJsonb = format!(r#"{{"a":[{}],"b":[{}]}}"#, list(0..2000), list(-2000..0))
        .parse()
        .unwrap();
    let path = parse_json_path(b"$ ? (@.a[*] < @.b[0])").unwrap();
    assert_eq!(values.as_raw().path_exists(&path), Ok(false));
    let path = parse_json_path(b"$ ? (@.a[*] < @.b[*])").unwrap();
    assert_eq!(
        values.as_raw().path_exists(&path),
        Err(Error::JsonPathTooComplex)
    );

    // Ordinary paths on large documents stay well within the budget, and
    // the budget is reset for every evaluation.
    let large: OwnedJsonb = format!(
        "[{}]",
        (0..300_000)
            .map(|i| format!("{{\"a\":{i}}}"))
            .collect::<Vec<_>>()
            .join(",")
    )
    .parse()
    .unwrap();
    let path = parse_json_path(b"$[*].a").unwrap();
    for _ in 0..3 {
        assert_eq!(large.as_raw().select_by_path(&path).unwrap().len(), 300_000);
    }
    let path = parse_json_path(b"$.**").unwrap();
    assert_eq!(large.as_raw().select_by_path(&path).unwrap().len(), 600_001);
}

#[test]
fn json_path_copies_are_bounded() {
    // Debug builds need more than the default stack to walk 500 levels.
    with_big_stack(|| {
        // Every ancestor of the string is selected and copied with it: 125,751
        // items, within the item budget, but about 300 MB of copies.
        let doc: OwnedJsonb = format!(
            "{}\"{}\"{}",
            "[".repeat(500),
            "x".repeat(1024),
            "]".repeat(500)
        )
        .parse()
        .unwrap();
        let path = parse_json_path(b"$.**.**").unwrap();
        let raw = doc.as_raw();
        assert_eq!(
            raw.select_by_path(&path).err(),
            Some(Error::JsonPathTooComplex)
        );
        assert_eq!(
            raw.select_array_by_path(&path).err(),
            Some(Error::JsonPathTooComplex)
        );
        assert_eq!(
            raw.select_value_by_path(&path).err(),
            Some(Error::JsonPathTooComplex)
        );
        // Checks that copy nothing are not limited by the byte budget.
        assert_eq!(raw.path_exists(&path), Ok(true));
        // A single `.**` copies 500 KiB, which is allowed.
        let path = parse_json_path(b"$.**").unwrap();
        assert_eq!(raw.select_by_path(&path).unwrap().len(), 501);
    });

    // Any single value can be copied, even one larger than 32 MiB, because
    // the budget includes the document size.
    let big: OwnedJsonb = format!(r#"{{"a":"{}","b":1}}"#, "x".repeat(33 << 20))
        .parse()
        .unwrap();
    let raw = big.as_raw();
    let path = parse_json_path(b"$.a").unwrap();
    assert_eq!(
        raw.select_first_by_path(&path).unwrap().unwrap().len(),
        // Scalar header and JEntry, then the string.
        8 + (33 << 20)
    );
    let path = parse_json_path(b"$").unwrap();
    assert_eq!(
        raw.select_first_by_path(&path).unwrap().unwrap().len(),
        raw.len()
    );
    // Copying it twice goes 33 MiB past the document size.
    let path = parse_json_path(b"$.**").unwrap();
    assert_eq!(
        raw.select_by_path(&path).err(),
        Some(Error::JsonPathTooComplex)
    );
}
