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
    from_slice, Date, Decimal128, Decimal256, Decimal64, Interval, Number, Object, Timestamp,
    TimestampTz, Value,
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
    let jsonb = jsonb::parse_value(json.as_bytes()).unwrap().to_vec();
    let corrupted = jsonb[0..jsonb.len() - 1].to_vec();
    let value = from_slice(corrupted.as_slice());
    assert!(value.is_err());
}
