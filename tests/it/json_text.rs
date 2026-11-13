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

//! `to_string` and `to_pretty_string` write JSON text without serde. Their
//! output must stay identical to serializing through serde_json, on valid and
//! on corrupted input.

use std::borrow::Cow;

use jsonb::{
    Date, Decimal128, Decimal256, Decimal64, Interval, Number, Object, RawJsonb, Timestamp,
    TimestampTz, Value,
};
use proptest::prelude::*;
use serde::Serialize;
use serde_json::ser::{CompactFormatter, Formatter, PrettyFormatter};

/// The output through `Serialize` and serde_json, or `None` on error.
fn serialize_with(raw: RawJsonb<'_>, formatter: impl Formatter) -> Option<String> {
    let mut buf = Vec::new();
    let mut serializer = serde_json::Serializer::with_formatter(&mut buf, formatter);
    raw.serialize(&mut serializer).ok()?;
    Some(String::from_utf8(buf).unwrap())
}

/// Checks both methods against serde_json, with the documented fallbacks.
fn assert_same_as_serde(data: &[u8]) {
    let raw = RawJsonb::new(data);
    let compact = serialize_with(raw, CompactFormatter).unwrap_or_else(|| {
        if data.is_empty() {
            "null".to_string()
        } else {
            String::from_utf8_lossy(data).into_owned()
        }
    });
    assert_eq!(raw.to_string(), compact, "to_string of {data:02x?}");
    let pretty = serialize_with(raw, PrettyFormatter::new()).unwrap_or_else(|| "null".into());
    assert_eq!(
        raw.to_pretty_string(),
        pretty,
        "to_pretty_string of {data:02x?}"
    );
}

/// Checks `data` and every copy of it with one byte replaced.
fn assert_same_as_serde_with_mutations(data: &[u8]) {
    assert_same_as_serde(data);
    let mut mutated = data.to_vec();
    for i in 0..data.len() {
        for byte in [0x00, 0xff, data[i] ^ 0x80, data[i] ^ 0x01] {
            mutated[i] = byte;
            assert_same_as_serde(&mutated);
        }
        mutated[i] = data[i];
    }
}

fn text() -> impl Strategy<Value = String> {
    // Escaped characters, control characters, multi-byte characters and `/`,
    // which serde_json does not escape.
    "[a-z \"\\\\/\u{0}-\u{1f}\u{7f}é中😀]{0,6}"
}

fn number() -> impl Strategy<Value = Number> {
    prop_oneof![
        any::<i64>().prop_map(Number::Int64),
        any::<u64>().prop_map(Number::UInt64),
        // Includes NaN and infinities, which serde_json writes as `null`.
        any::<f64>().prop_map(Number::Float64),
        (any::<u8>(), any::<i64>())
            .prop_map(|(scale, value)| Number::Decimal64(Decimal64 { scale, value })),
        (any::<u8>(), any::<i128>())
            .prop_map(|(scale, value)| Number::Decimal128(Decimal128 { scale, value })),
        // Large scales overflow the decimal formatting buffer, which is an error.
        (any::<u8>(), any::<i128>(), any::<i128>()).prop_map(|(scale, hi, lo)| {
            Number::Decimal256(Decimal256 {
                scale,
                value: ethnum::I256::from_words(hi, lo),
            })
        }),
    ]
}

fn value() -> impl Strategy<Value = Value<'static>> {
    let leaf = prop_oneof![
        Just(Value::Null),
        any::<bool>().prop_map(Value::Bool),
        number().prop_map(Value::Number),
        text().prop_map(|s| Value::String(Cow::Owned(s))),
        proptest::collection::vec(any::<u8>(), 0..4)
            .prop_map(|bytes| Value::Binary(Vec::leak(bytes))),
        (-100_000i32..100_000).prop_map(|value| Value::Date(Date { value })),
        (-1_000_000_000_000_000i64..1_000_000_000_000_000)
            .prop_map(|value| Value::Timestamp(Timestamp { value })),
        (
            -50_000i32..50_000,
            -1_000_000_000_000_000i64..1_000_000_000_000_000
        )
            .prop_map(|(offset, value)| Value::TimestampTz(TimestampTz { offset, value })),
        (any::<i32>(), any::<i32>(), any::<i64>()).prop_map(|(months, days, micros)| {
            Value::Interval(Interval {
                months,
                days,
                micros,
            })
        }),
    ];
    leaf.prop_recursive(4, 24, 4, |inner| {
        prop_oneof![
            proptest::collection::vec(inner.clone(), 0..4).prop_map(Value::Array),
            proptest::collection::btree_map(text(), inner, 0..4)
                .prop_map(|map| Value::Object(map.into_iter().collect::<Object>())),
        ]
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn json_text_matches_serde_json(value in value()) {
        assert_same_as_serde_with_mutations(&value.to_vec().unwrap());
    }
}

#[test]
fn json_text_matches_serde_json_on_edge_cases() {
    let documents = [
        r#"[]"#,
        r#"{}"#,
        r#"[[], {}, [[]], {"a": {}}]"#,
        r#"{"a": [1, {"b": [true, null]}], "": "", "c": {"d": {"e": []}}}"#,
        r#""\u0000\u001f\"\\/\b\f\n\r\t""#,
        r#"[-0.0, 1e300, -1e-300, 18446744073709551615, -9223372036854775808]"#,
        r#"[1.5, 123456789012345678901234567890.123456789, 0.000000000000000000001]"#,
    ];
    for text in documents {
        let jsonb = jsonb::parse_owned_jsonb(text.as_bytes()).unwrap();
        assert_same_as_serde_with_mutations(jsonb.as_ref());
    }
    assert_same_as_serde(&[]);
}

#[test]
fn json_text_matches_serde_json_at_the_nesting_limit() {
    // Debug builds use several KiB of stack per level in both writers, more
    // than the test thread's 2 MiB allows for `MAX_NESTING_DEPTH` levels.
    let run = || {
        // At the limit both succeed; past it both fail and fall back.
        for levels in [512, 513, 10_000] {
            let mut data = vec![0x80, 0x00, 0x00, 0x00];
            for _ in 1..levels {
                let len = data.len() as u32;
                let mut wrapper = vec![0x80, 0x00, 0x00, 0x01];
                wrapper.extend_from_slice(&(0x5000_0000 | len).to_be_bytes());
                wrapper.extend_from_slice(&data);
                data = wrapper;
            }
            assert_eq!(
                RawJsonb::new(&data).to_string().starts_with('['),
                levels == 512
            );
            assert_same_as_serde(&data);
        }
    };
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}
