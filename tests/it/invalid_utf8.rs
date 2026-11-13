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

//! Regression tests for string payloads that are not valid UTF-8.
//!
//! `RawJsonb` accepts arbitrary bytes through safe constructors, so every API
//! that exposes a JSONB string as `str` must reject invalid UTF-8.

use std::borrow::Cow;
use std::cmp::Ordering;

use jsonb::{from_raw_jsonb, from_slice, Error, OwnedJsonb, RawJsonb};
use proptest::prelude::*;
use serde::Deserialize;

/// Scalar string with payload `ff fe fd` (the reporter's input).
const SCALAR: &[u8] = &[
    0x20, 0x00, 0x00, 0x00, // scalar container header
    0x10, 0x00, 0x00, 0x03, // string JEntry, length 3
    0xff, 0xfe, 0xfd,
];

/// `[<invalid string>]`
const ARRAY_ELEMENT: &[u8] = &[
    0x80, 0x00, 0x00, 0x01, // array container header, 1 element
    0x10, 0x00, 0x00, 0x01, // string JEntry, length 1
    0xff,
];

/// `{<invalid key>: "v"}`
const OBJECT_KEY: &[u8] = &[
    0x40, 0x00, 0x00, 0x01, // object container header, 1 member
    0x10, 0x00, 0x00, 0x01, // key: string JEntry, length 1
    0x10, 0x00, 0x00, 0x01, // value: string JEntry, length 1
    0xff, b'v',
];

/// `{"k": <invalid string>}`
const OBJECT_VALUE: &[u8] = &[
    0x40, 0x00, 0x00, 0x01, // object container header, 1 member
    0x10, 0x00, 0x00, 0x01, // key: string JEntry, length 1
    0x10, 0x00, 0x00, 0x01, // value: string JEntry, length 1
    b'k', 0xff,
];

/// `[{"k": <invalid string>}]`
const NESTED: &[u8] = &[
    0x80, 0x00, 0x00, 0x01, // array container header, 1 element
    0x50, 0x00, 0x00, 0x0e, // container JEntry, length 14
    0x40, 0x00, 0x00, 0x01, // nested object header, 1 member
    0x10, 0x00, 0x00, 0x01, // key: string JEntry, length 1
    0x10, 0x00, 0x00, 0x01, // value: string JEntry, length 1
    b'k', 0xff,
];

const ALL: &[(&str, &[u8])] = &[
    ("scalar", SCALAR),
    ("array element", ARRAY_ELEMENT),
    ("object key", OBJECT_KEY),
    ("object value", OBJECT_VALUE),
    ("nested", NESTED),
];

#[test]
fn scalar_accessors_reject_invalid_utf8() {
    let raw = RawJsonb::new(SCALAR);
    assert_eq!(raw.as_str(), Err(Error::InvalidUtf8));
    assert_eq!(raw.to_str(), Err(Error::InvalidUtf8));
    assert_eq!(from_raw_jsonb::<String>(&raw), Err(Error::InvalidUtf8));
    assert_eq!(from_raw_jsonb::<char>(&raw), Err(Error::InvalidUtf8));
}

#[test]
fn to_value_rejects_invalid_utf8() {
    for (name, bytes) in ALL {
        let result = RawJsonb::new(bytes).to_value();
        assert_eq!(result, Err(Error::InvalidUtf8), "case {name}");
    }
}

#[test]
fn serde_deserialize_rejects_invalid_utf8() {
    #[derive(Debug, Deserialize)]
    #[allow(dead_code)]
    struct Member {
        k: String,
    }

    for (name, bytes) in ALL {
        let raw = RawJsonb::new(bytes);
        let result = from_raw_jsonb::<serde_json::Value>(&raw);
        assert_eq!(result.err(), Some(Error::InvalidUtf8), "case {name}");
    }
    let raw = RawJsonb::new(OBJECT_VALUE);
    let result = from_raw_jsonb::<Member>(&raw);
    assert_eq!(result.err(), Some(Error::InvalidUtf8));
}

#[test]
fn from_slice_rejects_invalid_utf8() {
    for (name, bytes) in ALL {
        assert!(from_slice(bytes).is_err(), "case {name}");
    }
}

#[test]
fn serialization_falls_back_without_exposing_invalid_utf8() {
    for (name, bytes) in ALL {
        let raw = RawJsonb::new(bytes);
        let expected = String::from_utf8_lossy(bytes).into_owned();
        assert_eq!(raw.to_string(), expected, "case {name}");
        assert_eq!(raw.to_pretty_string(), "null", "case {name}");
        assert!(serde_json::to_string(&raw).is_err(), "case {name}");
    }
}

#[test]
fn container_functions_reject_invalid_utf8() {
    let array = RawJsonb::new(ARRAY_ELEMENT);
    assert_eq!(array.array_values().err(), Some(Error::InvalidUtf8));
    assert_eq!(array.get_by_index(0).err(), Some(Error::InvalidUtf8));

    let key = RawJsonb::new(OBJECT_KEY);
    assert_eq!(key.object_keys().err(), Some(Error::InvalidUtf8));
    assert_eq!(key.object_each().err(), Some(Error::InvalidUtf8));

    let value = RawJsonb::new(OBJECT_VALUE);
    assert_eq!(value.object_each().err(), Some(Error::InvalidUtf8));
    assert_eq!(
        value.get_by_name("k", false).err(),
        Some(Error::InvalidUtf8)
    );
}

#[test]
fn comparison_orders_invalid_utf8_by_bytes() {
    // Comparison, `contains` and the comparable encoding read strings as bytes
    // without UTF-8 validation, which they do not need: UTF-8 orders byte-wise
    // like the characters it encodes. Invalid bytes therefore order by their
    // values instead of making the comparison fail.
    let valid_string = r#""a""#.parse::<OwnedJsonb>().unwrap();
    let invalid_string = RawJsonb::new(SCALAR);
    assert_eq!(
        invalid_string.partial_cmp(&valid_string.as_raw()),
        Some(Ordering::Greater)
    );
    assert_eq!(
        invalid_string.partial_cmp(&invalid_string),
        Some(Ordering::Equal)
    );
    assert!(invalid_string.contains(&invalid_string).unwrap());
    assert!(!invalid_string.convert_to_comparable().is_empty());

    let valid_object = r#"{"k": "v"}"#.parse::<OwnedJsonb>().unwrap();
    let invalid_key = RawJsonb::new(OBJECT_KEY);
    assert_eq!(
        invalid_key.partial_cmp(&valid_object.as_raw()),
        Some(Ordering::Greater)
    );
    assert!(!invalid_key.contains(&valid_object.as_raw()).unwrap());

    // APIs that expose the string still reject it.
    assert_eq!(invalid_string.as_str(), Err(Error::InvalidUtf8));
    assert!(serde_json::to_string(&invalid_key).is_err());
}

#[test]
fn unknown_jentry_type_returns_error_instead_of_panicking() {
    // Type code 0x7 is not assigned to any JSONB value kind.
    let bytes: &[u8] = &[0x80, 0x00, 0x00, 0x01, 0x70, 0x00, 0x00, 0x00];
    let raw = RawJsonb::new(bytes);
    assert_eq!(raw.array_values().err(), Some(Error::InvalidJsonb));
    assert_eq!(raw.get_by_index(0).err(), Some(Error::InvalidJsonb));
}

#[test]
fn valid_multibyte_strings_still_decode() {
    let owned = r#"{"键": ["测试", "é"]}"#.parse::<OwnedJsonb>().unwrap();
    let raw = owned.as_raw();
    assert_eq!(raw.to_string(), r#"{"键":["测试","é"]}"#);
    assert!(raw.to_value().is_ok());
    assert_eq!(raw.object_each().unwrap().unwrap()[0].0, "键");

    let scalar = r#""测试""#.parse::<OwnedJsonb>().unwrap();
    let raw = scalar.as_raw();
    assert_eq!(raw.as_str().unwrap(), Some(Cow::Borrowed("测试")));
    assert_eq!(from_raw_jsonb::<String>(&raw).unwrap(), "测试");
}

/// Encodes `payload` as a JSONB string in scalar, array, and object-value positions.
fn string_containers(payload: &[u8]) -> [Vec<u8>; 3] {
    let jentry = (0x1000_0000_u32 | payload.len() as u32).to_be_bytes();
    let scalar = [&0x2000_0000_u32.to_be_bytes()[..], &jentry, payload].concat();
    let array = [&0x8000_0001_u32.to_be_bytes()[..], &jentry, payload].concat();
    let key_jentry = 0x1000_0001_u32.to_be_bytes();
    let object = [
        &0x4000_0001_u32.to_be_bytes()[..],
        &key_jentry,
        &jentry,
        b"k",
        payload,
    ]
    .concat();
    [scalar, array, object]
}

proptest! {
    #[test]
    fn proptest_string_payload_validation(payload in proptest::collection::vec(any::<u8>(), 0..16)) {
        let expected = std::str::from_utf8(&payload).ok();
        let [scalar, array, object] = string_containers(&payload);

        let raw = RawJsonb::new(&scalar);
        let as_str = raw.as_str().ok().flatten();
        prop_assert_eq!(as_str.as_deref(), expected);
        let deserialized = from_raw_jsonb::<String>(&raw).ok();
        prop_assert_eq!(deserialized.as_deref(), expected);

        for bytes in [&scalar, &array, &object] {
            let raw = RawJsonb::new(bytes);
            prop_assert_eq!(raw.to_value().is_ok(), expected.is_some());
            prop_assert_eq!(from_raw_jsonb::<serde_json::Value>(&raw).is_ok(), expected.is_some());
            prop_assert_eq!(serde_json::to_string(&raw).is_ok(), expected.is_some());
        }
    }

    #[test]
    fn proptest_string_payload_after_ascii(
        prefix in proptest::collection::vec(0_u8..0x80, 0..150),
        middle in proptest::collection::vec(any::<u8>(), 0..6),
        suffix in proptest::collection::vec(0_u8..0x80, 0..20),
    ) {
        // Mostly ASCII, so both the ASCII fast path and `simdutf8` run, with
        // any bytes in between.
        assert_decodes_like_std(&[prefix, middle, suffix].concat());
    }
}

/// Checks that each way of decoding `payload` as a string accepts exactly
/// what `std::str::from_utf8` accepts.
fn assert_decodes_like_std(payload: &[u8]) {
    let expected = std::str::from_utf8(payload).ok();
    let [scalar, array, object] = string_containers(payload);

    let raw = RawJsonb::new(&scalar);
    let as_str = raw.as_str().ok().flatten();
    assert_eq!(as_str.as_deref(), expected, "{payload:?}");
    let deserialized = from_raw_jsonb::<String>(&raw).ok();
    assert_eq!(deserialized.as_deref(), expected, "{payload:?}");

    // The string starts at offset 8 in the scalar and the array and at 13 in
    // the object, so the word-at-a-time ASCII check starts at different
    // alignments.
    for bytes in [&scalar, &array, &object] {
        let raw = RawJsonb::new(bytes);
        assert_eq!(raw.to_value().is_ok(), expected.is_some(), "{payload:?}");
        assert_eq!(
            from_raw_jsonb::<serde_json::Value>(&raw).is_ok(),
            expected.is_some(),
            "{payload:?}"
        );
        assert_eq!(
            serde_json::to_string(&raw).is_ok(),
            expected.is_some(),
            "{payload:?}"
        );
    }
}

#[test]
fn ascii_fast_path_matches_std() {
    // An ASCII prefix, then one of these, then an ASCII suffix.
    let tails: [&[u8]; 12] = [
        b"",                 // all ASCII
        b"\x7f",             // the largest ASCII byte
        "é".as_bytes(),      // valid two-byte sequence
        "测".as_bytes(),     // valid three-byte sequence
        "😀".as_bytes(),     // valid four-byte sequence
        b"\x80",             // lone continuation byte
        b"\xc0\xaf",         // overlong encoding of '/'
        b"\xe0\x80\x80",     // overlong three-byte encoding
        b"\xed\xa0\x80",     // UTF-16 surrogate
        b"\xf4\x90\x80\x80", // above U+10FFFF
        b"\xf0\x9f\x98",     // truncated four-byte sequence
        b"\xff",             // never valid
    ];
    // Prefix lengths cross the 8-byte word that `is_ascii` checks at a time
    // and the 64 bytes below which `simdutf8` falls back to `std`.
    for prefix in 0..=130 {
        for tail in tails {
            for suffix in [0, 1, 9] {
                let mut payload = vec![b'a'; prefix];
                payload.extend_from_slice(tail);
                payload.extend(std::iter::repeat_n(b'z', suffix));
                assert_decodes_like_std(&payload);
            }
        }
    }
}
