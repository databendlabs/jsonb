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

use std::borrow::Cow;

use ethnum::I256;
use jsonb::{
    from_raw_jsonb, from_slice, Date, Decimal128, Decimal256, Decimal64, Error, Interval, Number,
    Object, OwnedJsonb, Timestamp, TimestampTz, Value,
};

#[test]
fn test_decode_null() {
    let s = b"\x20\0\0\0\0\0\0\0";
    let value = from_slice(s).unwrap();
    assert!(value.is_null());
    assert_eq!(value.as_null(), Some(()));
}

#[test]
fn test_decode_boolean() {
    let tests = vec![
        (b"\x20\0\0\0\x40\0\0\0".to_vec(), true),
        (b"\x20\0\0\0\x30\0\0\0".to_vec(), false),
    ];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_boolean());
        assert_eq!(value.as_bool().unwrap(), v);
    }
}

#[test]
fn test_decode_string() {
    let tests = vec![
        (b"\x20\0\0\0\x10\0\0\x03\x61\x73\x64".to_vec(), "asd"),
        (
            b"\x20\0\0\0\x10\0\0\x06\xE6\xB5\x8B\xE8\xAF\x95".to_vec(),
            "测试",
        ),
        (b"\x20\0\0\0\x10\0\0\x01\x0A".to_vec(), "\n"),
    ];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_string());
        assert_eq!(value.as_str().unwrap(), &Cow::from(v));
    }
}

#[test]
fn test_decode_int64() {
    let tests = vec![
        (b"\x20\0\0\0\x20\0\0\x01\x00".to_vec(), 0i64),
        (b"\x20\0\0\0\x20\0\0\x02\x40\x9C".to_vec(), -100i64),
        (b"\x20\0\0\0\x20\0\0\x02\x40\x80".to_vec(), i8::MIN as i64),
        (b"\x20\0\0\0\x20\0\0\x02\x40\x7F".to_vec(), i8::MAX as i64),
        (
            b"\x20\0\0\0\x20\0\0\x03\x40\x80\0".to_vec(),
            i16::MIN as i64,
        ),
        (
            b"\x20\0\0\0\x20\0\0\x03\x40\x7F\xFF".to_vec(),
            i16::MAX as i64,
        ),
        (
            b"\x20\0\0\0\x20\0\0\x05\x40\x80\0\0\0".to_vec(),
            i32::MIN as i64,
        ),
        (
            b"\x20\0\0\0\x20\0\0\x05\x40\x7F\xFF\xFF\xFF".to_vec(),
            i32::MAX as i64,
        ),
        (
            b"\x20\0\0\0\x20\0\0\x09\x40\x80\0\0\0\0\0\0\0".to_vec(),
            i64::MIN,
        ),
        (
            b"\x20\0\0\0\x20\0\0\x09\x40\x7F\xFF\xFF\xFF\xFF\xFF\xFF\xFF".to_vec(),
            i64::MAX,
        ),
    ];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_i64());
        assert_eq!(value.as_i64().unwrap(), v);
    }
}

#[test]
fn test_decode_uint64() {
    let tests = vec![
        (b"\x20\0\0\0\x20\0\0\x01\x00".to_vec(), 0u64),
        (b"\x20\0\0\0\x20\0\0\x02\x50\x64".to_vec(), 100u64),
        (b"\x20\0\0\0\x20\0\0\x02\x50\xFF".to_vec(), u8::MAX as u64),
        (
            b"\x20\0\0\0\x20\0\0\x03\x50\xFF\xFF".to_vec(),
            u16::MAX as u64,
        ),
        (
            b"\x20\0\0\0\x20\0\0\x05\x50\xFF\xFF\xFF\xFF".to_vec(),
            u32::MAX as u64,
        ),
        (
            b"\x20\0\0\0\x20\0\0\x09\x50\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF".to_vec(),
            u64::MAX,
        ),
    ];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_u64());
        assert_eq!(value.as_u64().unwrap(), v);
    }
}

#[test]
fn test_decode_float64() {
    let tests = vec![
        (b"\x20\0\0\0\x20\0\0\x01\x20".to_vec(), f64::INFINITY),
        (b"\x20\0\0\0\x20\0\0\x01\x30".to_vec(), f64::NEG_INFINITY),
        (
            b"\x20\0\0\0\x20\0\0\x09\x60\x3F\x89\x30\xBE\x0D\xED\x28\x8D".to_vec(),
            0.0123f64,
        ),
        (
            b"\x20\0\0\0\x20\0\0\x09\x60\x7F\xE5\x5C\x57\x6D\x81\x57\x26".to_vec(),
            1.2e308f64,
        ),
    ];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_f64());
        assert_eq!(value.as_f64().unwrap(), v);
    }
}

#[test]
fn test_decode_deprected_decimal() {
    // Compatible with deprecated Decimal128 and Decimal256 formats, including precision
    let tests = vec![
        (b"\x20\0\0\0\x20\0\0\x13\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x04\xD2\x26\x02".to_vec(), Number::Decimal128(Decimal128 {
            scale: 2,
            value: 1234
        })),
        (b"\x20\0\0\0\x20\0\0\x13\x70\0\0\0\0\0\0\0\0\0\0\x09\x18\x4E\x72\xA1\xE5\x26\x0A".to_vec(), Number::Decimal128(Decimal128 {
            scale: 10,
            value: 10000000000485
        })),
        (b"\x20\0\0\0\x20\0\0\x23\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x04\xD2\x4C\x02".to_vec(),
        Number::Decimal256(Decimal256 { scale: 2, value: I256::new(1234) })),
        (b"\x20\0\0\0\x20\0\0\x23\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x09\x18\x4E\x72\xA1\xE5\x4C\x0A".to_vec(),
            Number::Decimal256(Decimal256 { scale: 10, value: I256::new(10000000000485) })),
    ];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_number());
        assert_eq!(value.as_number().unwrap(), v);
    }
}

#[test]
fn test_decode_decimal() {
    let tests = vec![
        (b"\x20\0\0\0\x20\0\0\x0A\x70\0\0\0\0\0\0\x04\xD2\x02".to_vec(), Number::Decimal64(Decimal64 {
            scale: 2,
            value: 1234
        })),
        (b"\x20\0\0\0\x20\0\0\x12\x70\0\0\0\0\0\0\0\0\0\0\x09\x18\x4E\x72\xA1\xE5\x0A".to_vec(), Number::Decimal128(Decimal128 {
            scale: 10,
            value: 10000000000485
        })),
        (b"\x20\0\0\0\x20\0\0\x22\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x04\xD2\x02".to_vec(),
        Number::Decimal256(Decimal256 { scale: 2, value: I256::new(1234) })),
        (b"\x20\0\0\0\x20\0\0\x22\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x09\x18\x4E\x72\xA1\xE5\x0A".to_vec(),
            Number::Decimal256(Decimal256 { scale: 10, value: I256::new(10000000000485) })),
    ];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_number());
        assert_eq!(value.as_number().unwrap(), v);
    }
}

/// Every encoder keeps a decimal's scale and digits within the precision of
/// its width, 18, 38 or 76. Decoding used to accept any `u8` scale and any
/// value, which made callers overflow `10^scale`.
#[test]
fn decimals_beyond_their_precision_are_invalid() {
    let e18 = 10_i64.pow(18);
    let e38 = 10_i128.pow(38);
    let e76 = I256::from(10).pow(76);
    let valid = [
        Number::Decimal64(Decimal64 {
            scale: 18,
            value: e18 - 1,
        }),
        Number::Decimal64(Decimal64 {
            scale: 0,
            value: 1 - e18,
        }),
        Number::Decimal128(Decimal128 {
            scale: 38,
            value: e38 - 1,
        }),
        Number::Decimal128(Decimal128 {
            scale: 0,
            value: 1 - e38,
        }),
        Number::Decimal256(Decimal256 {
            scale: 76,
            value: e76 - 1,
        }),
        Number::Decimal256(Decimal256 {
            scale: 0,
            value: I256::ONE - e76,
        }),
    ];
    for number in valid {
        let data = Value::Number(number.clone()).to_vec().unwrap();
        assert_eq!(from_slice(&data).unwrap(), Value::Number(number));
    }
    let invalid = [
        Number::Decimal64(Decimal64 {
            scale: 19,
            value: 1,
        }),
        Number::Decimal64(Decimal64 {
            scale: 255,
            value: 1,
        }),
        Number::Decimal64(Decimal64 {
            scale: 0,
            value: e18,
        }),
        Number::Decimal64(Decimal64 {
            scale: 2,
            value: i64::MIN,
        }),
        Number::Decimal128(Decimal128 {
            scale: 39,
            value: 1,
        }),
        Number::Decimal128(Decimal128 {
            scale: 0,
            value: e38,
        }),
        Number::Decimal128(Decimal128 {
            scale: 0,
            value: -e38,
        }),
        Number::Decimal256(Decimal256 {
            scale: 77,
            value: I256::ONE,
        }),
        Number::Decimal256(Decimal256 {
            scale: 0,
            value: e76,
        }),
        Number::Decimal256(Decimal256 {
            scale: 0,
            value: I256::MIN,
        }),
    ];
    for number in invalid {
        let data = Value::Number(number.clone()).to_vec().unwrap();
        assert!(from_slice(&data).is_err(), "{number:?}");
    }
    // The deprecated widths, which also store a precision byte before the
    // scale, with scales 39 and 77.
    let deprecated = [
        b"\x20\0\0\0\x20\0\0\x13\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x04\xD2\x26\x27".to_vec(),
        b"\x20\0\0\0\x20\0\0\x23\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x04\xD2\x4C\x4D".to_vec(),
    ];
    for data in deprecated {
        assert!(from_slice(&data).is_err(), "{data:02x?}");
    }
}

#[test]
fn test_decode_array() {
    let tests = vec![(
        b"\x80\0\0\x02\x30\0\0\0\x40\0\0\0".to_vec(),
        vec![Value::Bool(false), Value::Bool(true)],
    )];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_array());
        let arr = value.as_array().unwrap();
        assert_eq!(arr.len(), v.len());
        for (l, r) in arr.iter().zip(v.iter()) {
            assert_eq!(l, r);
        }
    }
}

#[test]
fn test_decode_object() {
    let mut obj1 = Object::new();
    obj1.insert("asd".to_string(), Value::String(Cow::from("adf")));
    let tests = vec![(
        b"\x40\0\0\x01\x10\0\0\x03\x10\0\0\x03\x61\x73\x64\x61\x64\x66".to_vec(),
        obj1,
    )];
    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert!(value.is_object());
        let obj = value.as_object().unwrap();
        assert_eq!(obj.len(), v.len());
        for ((lk, lv), (rk, rv)) in obj.iter().enumerate().zip(v.iter().enumerate()) {
            assert_eq!(lk, rk);
            assert_eq!(lv, rv);
        }
    }
}

#[test]
fn test_decode_extension() {
    let tests = vec![
        (
            b"\x20\0\0\0\x60\0\0\x04\0\x01\x02\x03".to_vec(),
            Value::Binary(&[1, 2, 3]),
        ),
        (
            b"\x20\0\0\0\x60\0\0\x05\x10\0\0\x4f\x94".to_vec(),
            Value::Date(Date { value: 20372 }),
        ),
        (
            b"\x20\0\0\0\x60\0\0\x09\x20\0\x06\x40\xd6\xb7\x23\x80\0".to_vec(),
            Value::Timestamp(Timestamp {
                value: 1760140800000000,
            }),
        ),
        // Backward-compatible implementation with offset as int8 hours
        (
            b"\x20\0\0\0\x60\0\0\x0a\x30\0\x06\x40\xd6\xb7\x23\x80\0\x08".to_vec(),
            Value::TimestampTz(TimestampTz {
                offset: 8 * 3600,
                value: 1760140800000000,
            }),
        ),
        (
            b"\x20\0\0\0\x60\0\0\x0d\x30\0\x06\x40\xd6\xb7\x23\x80\0\0\0\x70\x80".to_vec(),
            Value::TimestampTz(TimestampTz {
                offset: 8 * 3600,
                value: 1760140800000000,
            }),
        ),
        (
            b"\x20\0\0\0\x60\0\0\x11\x40\0\0\0\x0A\0\0\0\x14\0\0\0\0\x11\xE1\xA3\0".to_vec(),
            Value::Interval(Interval {
                months: 10,
                days: 20,
                micros: 300000000,
            }),
        ),
    ];

    for (s, v) in tests {
        let value = from_slice(s.as_slice()).unwrap();
        assert_eq!(value, v);
    }
}

#[test]
fn test_decode_corrupted() {
    let json = "{\"a\": 1, \"b\": \"123\"}";
    let jsonb = jsonb::parse_value(json.as_bytes())
        .unwrap()
        .to_vec()
        .unwrap();
    let corrupted = jsonb[0..jsonb.len() - 1].to_vec();
    let value = from_slice(corrupted.as_slice());
    assert!(value.is_err());
}

#[test]
fn deserialize_char_accepts_one_character_of_any_width() {
    // `deserialize_char` used to compare the length in bytes with 1, so it
    // rejected every non-ASCII character.
    for (text, expect) in [("a", 'a'), ("é", 'é'), ("中", '中'), ("😀", '😀')] {
        let jsonb = jsonb::OwnedJsonb::new(Value::String(Cow::Borrowed(text)).to_vec().unwrap());
        assert_eq!(jsonb::from_raw_jsonb::<char>(&jsonb.as_raw()), Ok(expect));
    }
    for text in ["", "ab", "é!", "😀😀"] {
        let jsonb = jsonb::OwnedJsonb::new(Value::String(Cow::Borrowed(text)).to_vec().unwrap());
        assert!(
            jsonb::from_raw_jsonb::<char>(&jsonb.as_raw()).is_err(),
            "{text:?}"
        );
    }
}

/// Reads the first value of an object, or with `KEY_ONLY` only its first
/// key, and then stops.
struct FirstOfMap<const KEY_ONLY: bool>;

impl<'de, const KEY_ONLY: bool> serde::Deserialize<'de> for FirstOfMap<KEY_ONLY> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Visit<const KEY_ONLY: bool>;
        impl<'de, const KEY_ONLY: bool> serde::de::Visitor<'de> for Visit<KEY_ONLY> {
            type Value = FirstOfMap<KEY_ONLY>;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("a map")
            }
            fn visit_map<A: serde::de::MapAccess<'de>>(
                self,
                mut map: A,
            ) -> Result<Self::Value, A::Error> {
                if KEY_ONLY {
                    map.next_key::<String>()?;
                } else {
                    map.next_entry::<String, String>()?;
                }
                Ok(FirstOfMap)
            }
        }
        deserializer.deserialize_map(Visit::<KEY_ONLY>)
    }
}

#[test]
fn deserializing_part_of_a_container_fails() {
    // A tuple read two of the three numbers and stopped, so "x" was read at
    // the third number's payload and came out as "P", the byte 0x50 that
    // tags an unsigned integer.
    #[derive(Debug, serde::Deserialize)]
    #[allow(dead_code)]
    struct Outer {
        a: ((i32, i32), String),
    }
    let doc: OwnedJsonb = r#"{"a": [[1, 2, 3], "x"]}"#.parse().unwrap();
    let result = from_raw_jsonb::<Outer>(&doc.as_raw());
    assert!(
        matches!(&result, Err(Error::Message(m)) if m.contains("invalid length 3")),
        "{result:?}"
    );

    // A map visitor that stopped early used to succeed, and the members it
    // skipped were never checked, so an invalid key went unnoticed.
    let two: jsonb::OwnedJsonb = r#"{"a": "1", "b": "2"}"#.parse().unwrap();
    let one: jsonb::OwnedJsonb = r#"{"a": "1"}"#.parse().unwrap();
    // `{"a": "1", null: "2"}`.
    let words = [
        0x4000_0002_u32,
        0x1000_0001,
        0x0000_0000,
        0x1000_0001,
        0x1000_0001,
    ];
    let mut bad_key: Vec<u8> = words.iter().flat_map(|w| w.to_be_bytes()).collect();
    bad_key.extend_from_slice(b"a12");
    for (name, bytes) in [("two", two.as_ref()), ("bad key", &bad_key[..])] {
        let raw = jsonb::RawJsonb::new(bytes);
        let result = jsonb::from_raw_jsonb::<FirstOfMap<false>>(&raw);
        assert!(
            matches!(&result, Err(jsonb::Error::Message(m)) if m.contains("invalid length 2")),
            "{name}: {:?}",
            result.err()
        );
    }
    // A key read without its value leaves the member unread too.
    let result = jsonb::from_raw_jsonb::<FirstOfMap<true>>(&one.as_raw());
    assert!(
        matches!(&result, Err(jsonb::Error::Message(m)) if m.contains("invalid length 1")),
        "{:?}",
        result.err()
    );
    // Reading every member still works.
    assert!(jsonb::from_raw_jsonb::<FirstOfMap<false>>(&one.as_raw()).is_ok());
}

/// The `size_hint` of a sequence or map before each element and after the last.
#[derive(Debug, PartialEq)]
struct SizeHints(Vec<Option<usize>>);

impl<'de> serde::Deserialize<'de> for SizeHints {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Visit;
        impl<'de> serde::de::Visitor<'de> for Visit {
            type Value = SizeHints;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("a sequence or a map")
            }
            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> Result<SizeHints, A::Error> {
                let mut hints = vec![seq.size_hint()];
                while seq.next_element::<serde::de::IgnoredAny>()?.is_some() {
                    hints.push(seq.size_hint());
                }
                Ok(SizeHints(hints))
            }
            fn visit_map<A: serde::de::MapAccess<'de>>(
                self,
                mut map: A,
            ) -> Result<SizeHints, A::Error> {
                let mut hints = vec![map.size_hint()];
                while map
                    .next_entry::<serde::de::IgnoredAny, serde::de::IgnoredAny>()?
                    .is_some()
                {
                    hints.push(map.size_hint());
                }
                Ok(SizeHints(hints))
            }
        }
        deserializer.deserialize_any(Visit)
    }
}

#[test]
fn deserializer_size_hints_count_the_members_left() {
    // The hint stayed at the container's length after members were read.
    let array: jsonb::OwnedJsonb = "[1, 2, 3]".parse().unwrap();
    assert_eq!(
        jsonb::from_raw_jsonb::<SizeHints>(&array.as_raw()),
        Ok(SizeHints(vec![Some(3), Some(2), Some(1), Some(0)]))
    );
    let object: jsonb::OwnedJsonb = r#"{"a": 1, "b": 2}"#.parse().unwrap();
    assert_eq!(
        jsonb::from_raw_jsonb::<SizeHints>(&object.as_raw()),
        Ok(SizeHints(vec![Some(2), Some(1), Some(0)]))
    );
}

#[test]
fn deserializing_a_container_checks_the_member_type() {
    use std::collections::HashMap;
    // The string "@\0\0\0" has the bytes of an empty object header. Reading a
    // map from an array member used to parse the member's payload as a
    // header without checking its type, so this string read as `{}`.
    let text: OwnedJsonb = r#"["@\u0000\u0000\u0000"]"#.parse().unwrap();
    assert_eq!(
        from_raw_jsonb::<Vec<HashMap<String, i32>>>(&text.as_raw()),
        Err(Error::UnexpectedType)
    );
    // A null member has no payload, so the next member's payload was read as
    // the header, and the string after it then read past the end.
    let pair: OwnedJsonb = r#"[null, "@\u0000\u0000\u0000"]"#.parse().unwrap();
    assert_eq!(
        from_raw_jsonb::<(HashMap<String, i32>, String)>(&pair.as_raw()),
        Err(Error::UnexpectedType)
    );
    let numbers: OwnedJsonb = "[1]".parse().unwrap();
    assert_eq!(
        from_raw_jsonb::<Vec<Vec<i32>>>(&numbers.as_raw()),
        Err(Error::UnexpectedType)
    );
}
