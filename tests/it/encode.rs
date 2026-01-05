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
    Date, Decimal128, Decimal256, Decimal64, Interval, Number, Object, Timestamp, TimestampTz,
    Value,
};

#[test]
fn test_encode_null() {
    assert_eq!(&Value::Null.to_vec(), b"\x20\0\0\0\0\0\0\0");
}

#[test]
fn test_encode_boolean() {
    assert_eq!(&Value::Bool(true).to_vec(), b"\x20\0\0\0\x40\0\0\0");
    assert_eq!(&Value::Bool(false).to_vec(), b"\x20\0\0\0\x30\0\0\0");
}

#[test]
fn test_encode_string() {
    assert_eq!(
        &Value::String(Cow::from("asd")).to_vec(),
        b"\x20\0\0\0\x10\0\0\x03\x61\x73\x64"
    );
    assert_eq!(
        &Value::String(Cow::from("测试")).to_vec(),
        b"\x20\0\0\0\x10\0\0\x06\xE6\xB5\x8B\xE8\xAF\x95"
    );
}

#[test]
fn test_encode_int64() {
    assert_eq!(
        &Value::Number(Number::Int64(0)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x01\x00"
    );
    assert_eq!(
        &Value::Number(Number::Int64(-100)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x02\x40\x9C"
    );
    assert_eq!(
        &Value::Number(Number::Int64(i8::MIN as i64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x02\x40\x80"
    );
    assert_eq!(
        &Value::Number(Number::Int64(i8::MAX as i64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x02\x40\x7F"
    );
    assert_eq!(
        &Value::Number(Number::Int64(i16::MIN as i64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x03\x40\x80\0"
    );
    assert_eq!(
        &Value::Number(Number::Int64(i16::MAX as i64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x03\x40\x7F\xFF"
    );
    assert_eq!(
        &Value::Number(Number::Int64(i32::MIN as i64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x05\x40\x80\0\0\0"
    );
    assert_eq!(
        &Value::Number(Number::Int64(i32::MAX as i64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x05\x40\x7F\xFF\xFF\xFF"
    );
    assert_eq!(
        &Value::Number(Number::Int64(i64::MIN)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x09\x40\x80\0\0\0\0\0\0\0"
    );
    assert_eq!(
        &Value::Number(Number::Int64(i64::MAX)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x09\x40\x7F\xFF\xFF\xFF\xFF\xFF\xFF\xFF"
    );
}

#[test]
fn test_encode_uint64() {
    assert_eq!(
        &Value::Number(Number::UInt64(0)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x01\x00"
    );
    assert_eq!(
        &Value::Number(Number::UInt64(100)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x02\x50\x64"
    );
    assert_eq!(
        &Value::Number(Number::UInt64(u8::MAX as u64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x02\x50\xFF"
    );
    assert_eq!(
        &Value::Number(Number::UInt64(u16::MAX as u64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x03\x50\xFF\xFF"
    );
    assert_eq!(
        &Value::Number(Number::UInt64(u32::MAX as u64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x05\x50\xFF\xFF\xFF\xFF"
    );
    assert_eq!(
        &Value::Number(Number::UInt64(u64::MAX)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x09\x50\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF"
    );
}

#[test]
fn test_encode_float64() {
    assert_eq!(
        &Value::Number(Number::Float64(f64::INFINITY)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x01\x20"
    );
    assert_eq!(
        &Value::Number(Number::Float64(f64::NEG_INFINITY)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x01\x30"
    );
    assert_eq!(
        &Value::Number(Number::Float64(0.0123f64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x09\x60\x3F\x89\x30\xBE\x0D\xED\x28\x8D"
    );
    assert_eq!(
        &Value::Number(Number::Float64(1.2e308f64)).to_vec(),
        b"\x20\0\0\0\x20\0\0\x09\x60\x7F\xE5\x5C\x57\x6D\x81\x57\x26"
    );
}

#[test]
fn test_encode_decimal() {
    assert_eq!(
        &Value::Number(Number::Decimal64(Decimal64 {
            scale: 2,
            value: 1234
        }))
        .to_vec(),
        b"\x20\0\0\0\x20\0\0\x0A\x70\0\0\0\0\0\0\x04\xD2\x02"
    );
    assert_eq!(
        &Value::Number(Number::Decimal128(Decimal128 {
            scale: 10,
            value: 10000000000485
        }))
        .to_vec(),
        b"\x20\0\0\0\x20\0\0\x12\x70\0\0\0\0\0\0\0\0\0\0\x09\x18\x4E\x72\xA1\xE5\x0A"
    );

    assert_eq!(
        &Value::Number(Number::Decimal256(Decimal256 { scale: 2, value: I256::new(1234) })).to_vec(),
        b"\x20\0\0\0\x20\0\0\x22\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x04\xD2\x02"
    );
    assert_eq!(
        &Value::Number(Number::Decimal256(Decimal256 { scale: 10, value: I256::new(10000000000485) })).to_vec(),
        b"\x20\0\0\0\x20\0\0\x22\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x09\x18\x4E\x72\xA1\xE5\x0A"
    );
}

#[test]
fn test_encode_array() {
    assert_eq!(
        &Value::Array(vec![Value::Bool(false), Value::Bool(true)]).to_vec(),
        b"\x80\0\0\x02\x30\0\0\0\x40\0\0\0",
    );

    assert_eq!(
        &Value::Array(vec![
            Value::Bool(false),
            Value::Binary(&[100, 101, 102, 103]),
            Value::Date(Date {value: 20381 }),
            Value::Timestamp(Timestamp { value: 1540230120000000 }),
            Value::TimestampTz(TimestampTz { offset: 8 * 3600, value: 1670389100000000 }),
            Value::Interval(Interval { months: 2, days: 10, micros: 500000000 }),
            Value::Number(Number::Decimal256(Decimal256 { scale: 2, value: I256::new(1234) })),
        ]).to_vec(),
        b"\x80\0\0\x07\x30\0\0\0\x60\0\0\x05\x60\0\0\x05\x60\0\0\x09\x60\0\0\x0D\x60\0\0\x11\x20\0\0\x22\0\x64\x65\x66\x67\x10\0\0\x4F\x9D\x20\0\x05\x78\xD4\xC5\x2C\xCA\0\x30\0\x05\xEF\x35\xC4\xF1\x33\0\0\0\x70\x80\x40\0\0\0\x02\0\0\0\x0A\0\0\0\0\x1D\xCD\x65\0\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x04\xD2\x02",
    );
}

#[test]
fn test_encode_object() {
    let mut obj1 = Object::new();
    obj1.insert("asd".to_string(), Value::String(Cow::from("adf")));
    assert_eq!(
        &Value::Object(obj1).to_vec(),
        b"\x40\0\0\x01\x10\0\0\x03\x10\0\0\x03\x61\x73\x64\x61\x64\x66"
    );

    let mut obj2 = Object::new();
    obj2.insert("k1".to_string(), Value::String(Cow::from("v1")));
    obj2.insert("k2".to_string(), Value::Binary(&[200, 201, 202, 203]));
    obj2.insert("k3".to_string(), Value::Date(Date { value: 20381 }));
    obj2.insert(
        "k4".to_string(),
        Value::Timestamp(Timestamp {
            value: 1540230120000000,
        }),
    );
    obj2.insert(
        "k5".to_string(),
        Value::TimestampTz(TimestampTz {
            offset: 8 * 3600,
            value: 1670389100000000,
        }),
    );
    obj2.insert(
        "k6".to_string(),
        Value::Interval(Interval {
            months: 2,
            days: 10,
            micros: 500000000,
        }),
    );
    obj2.insert(
        "k7".to_string(),
        Value::Number(Number::Decimal256(Decimal256 {
            scale: 2,
            value: I256::new(1234),
        })),
    );

    assert_eq!(
        &Value::Object(obj2).to_vec(),
        b"\x40\0\0\x07\x10\0\0\x02\x10\0\0\x02\x10\0\0\x02\x10\0\0\x02\x10\0\0\x02\x10\0\0\x02\x10\0\0\x02\x10\0\0\x02\x60\0\0\x05\x60\0\0\x05\x60\0\0\x09\x60\0\0\x0D\x60\0\0\x11\x20\0\0\x22\x6B\x31\x6B\x32\x6B\x33\x6B\x34\x6B\x35\x6B\x36\x6B\x37\x76\x31\0\xC8\xC9\xCA\xCB\x10\0\0\x4F\x9D\x20\0\x05\x78\xD4\xC5\x2C\xCA\0\x30\0\x05\xEF\x35\xC4\xF1\x33\0\0\0\x70\x80\x40\0\0\0\x02\0\0\0\x0A\0\0\0\0\x1D\xCD\x65\0\x70\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x04\xD2\x02"
    );
}

#[test]
fn test_encode_extension() {
    assert_eq!(
        Value::Binary(&[1, 2, 3]).to_vec(),
        b"\x20\0\0\0\x60\0\0\x04\0\x01\x02\x03"
    );
    assert_eq!(
        Value::Date(Date { value: 20372 }).to_vec(),
        b"\x20\0\0\0\x60\0\0\x05\x10\0\0\x4f\x94"
    );
    assert_eq!(
        Value::Timestamp(Timestamp {
            value: 1760140800000000
        })
        .to_vec(),
        b"\x20\0\0\0\x60\0\0\x09\x20\0\x06\x40\xd6\xb7\x23\x80\0"
    );
    assert_eq!(
        Value::TimestampTz(TimestampTz {
            offset: 8 * 3600,
            value: 1760140800000000
        })
        .to_vec(),
        b"\x20\0\0\0\x60\0\0\x0d\x30\0\x06\x40\xd6\xb7\x23\x80\0\0\0\x70\x80"
    );
    assert_eq!(
        Value::Interval(Interval {
            months: 10,
            days: 20,
            micros: 300000000
        })
        .to_vec(),
        b"\x20\0\0\0\x60\0\0\x11\x40\0\0\0\x0A\0\0\0\x14\0\0\0\0\x11\xE1\xA3\0"
    );
}
