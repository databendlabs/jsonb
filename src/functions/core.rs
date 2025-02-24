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

// This file contains the fundamental functions.

use core::convert::TryInto;
use std::cmp::Ordering;
use std::collections::VecDeque;

use crate::constants::*;
use crate::error::*;
use crate::jentry::JEntry;
use crate::number::Number;
use serde::Serialize;

use crate::RawJsonb;

impl RawJsonb<'_> {
    /// Converts the JSONB value to a JSON string.
    ///
    /// This function serializes the JSONB value into a human-readable JSON string representation.
    /// It handles both container types (objects and arrays) and scalar types. If the JSONB data is invalid,
    /// it attempts to parse it as text JSON and falls back to "null" if parsing fails.
    ///
    /// # Returns
    ///
    /// * `String` - The JSON string representation of the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_string(), "[1,2,3]");
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": "hello"}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_string(), r#"{"a":1,"b":"hello"}"#);
    ///
    /// let num_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = num_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_string(), "123.45");
    ///
    /// let string_jsonb = r#""hello, world!""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = string_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_string(), r#""hello, world!""#);
    ///
    /// let true_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = true_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_string(), "true");
    ///
    /// // Example with invalid JSONB data (fallback to text JSON parsing)
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]); // Invalid binary JSONB
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    ///
    /// // It will try to parse it as text JSON, in this case fails and return "null"
    /// assert_eq!(invalid_raw_jsonb.to_string(), "null");
    /// ```
    #[allow(clippy::inherent_to_string)]
    pub fn to_string(&self) -> String {
        let mut buf = Vec::with_capacity(self.len());
        let formatter = serde_json::ser::CompactFormatter {};
        let mut ser = serde_json::Serializer::with_formatter(&mut buf, formatter);
        match self.serialize(&mut ser) {
            Ok(_) => String::from_utf8(buf).unwrap(),
            Err(_) => "null".to_string(),
        }
    }

    /// Converts the JSONB value to a pretty-printed JSON string.
    ///
    /// This function serializes the JSONB value into a human-readable JSON string representation with indentation for formatting.
    /// Like `to_string()`, it handles both container types (objects and arrays) and scalar types.
    /// If the JSONB data is invalid, it attempts to parse it as text JSON, pretty-prints the result if successful,
    /// and falls back to "null" if either binary or text JSON parsing fails.
    ///
    /// # Returns
    ///
    /// * `String` - The pretty-printed JSON string representation of the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_pretty_string(), "[\n  1,\n  2,\n  3\n]");
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": "hello"}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_pretty_string(), "{\n  \"a\": 1,\n  \"b\": \"hello\"\n}");
    ///
    /// let num_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = num_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_pretty_string(), "123.45");
    ///
    /// let string_jsonb = r#""hello, world!""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = string_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_pretty_string(), r#""hello, world!""#);
    ///
    /// // Example with invalid JSONB data (fallback to text JSON parsing)
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]); // Invalid binary JSONB
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// assert_eq!(invalid_raw_jsonb.to_pretty_string(), "null"); // Fails and returns "null"
    /// ```
    pub fn to_pretty_string(&self) -> String {
        let mut buf = Vec::with_capacity(self.len());
        let formatter = serde_json::ser::PrettyFormatter::new();
        let mut ser = serde_json::Serializer::with_formatter(&mut buf, formatter);
        match self.serialize(&mut ser) {
            Ok(_) => String::from_utf8(buf).unwrap(),
            Err(_) => "null".to_string(),
        }
    }
}

impl Eq for RawJsonb<'_> {}

/// Implements `PartialOrd` for `RawJsonb`, allowing comparison of two `RawJsonb` values.
///
/// The comparison logic handles different JSONB types (scalar, array, object) and considers null values.
/// The ordering is defined as follows:
///
/// 1. Null is considered greater than any other type.
/// 2. Scalars are compared based on their type and value (String > Number > Boolean).
/// 3. Arrays are compared element by element.
/// 4. Objects are compared based on their keys and values.
/// 5. Arrays are greater than objects and scalars.
/// 6. Objects are greater than scalars.
/// 7. If the types are incompatible, None is returned.
#[allow(clippy::non_canonical_partial_ord_impl)]
impl PartialOrd for RawJsonb<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let left = self.data;
        let right = other.data;
        let left_header = read_u32(left, 0).ok()?;
        let right_header = read_u32(right, 0).ok()?;
        match (
            left_header & CONTAINER_HEADER_TYPE_MASK,
            right_header & CONTAINER_HEADER_TYPE_MASK,
        ) {
            (SCALAR_CONTAINER_TAG, SCALAR_CONTAINER_TAG) => {
                let left_encoded = read_u32(left, 4).ok()?;
                let left_jentry = JEntry::decode_jentry(left_encoded);
                let right_encoded = read_u32(right, 4).ok()?;
                let right_jentry = JEntry::decode_jentry(right_encoded);
                compare_scalar(&left_jentry, &left[8..], &right_jentry, &right[8..])
            }
            (ARRAY_CONTAINER_TAG, ARRAY_CONTAINER_TAG) => {
                compare_array(left_header, &left[4..], right_header, &right[4..])
            }
            (OBJECT_CONTAINER_TAG, OBJECT_CONTAINER_TAG) => {
                compare_object(left_header, &left[4..], right_header, &right[4..])
            }
            (SCALAR_CONTAINER_TAG, ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG) => {
                let left_encoded = read_u32(left, 4).ok()?;
                let left_jentry = JEntry::decode_jentry(left_encoded);
                match left_jentry.type_code {
                    NULL_TAG => Some(Ordering::Greater),
                    _ => Some(Ordering::Less),
                }
            }
            (ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG, SCALAR_CONTAINER_TAG) => {
                let right_encoded = read_u32(right, 4).ok()?;
                let right_jentry = JEntry::decode_jentry(right_encoded);
                match right_jentry.type_code {
                    NULL_TAG => Some(Ordering::Less),
                    _ => Some(Ordering::Greater),
                }
            }
            (ARRAY_CONTAINER_TAG, OBJECT_CONTAINER_TAG) => Some(Ordering::Greater),
            (OBJECT_CONTAINER_TAG, ARRAY_CONTAINER_TAG) => Some(Ordering::Less),
            (_, _) => None,
        }
    }
}

/// Implements `Ord` for `RawJsonb`, allowing comparison of two `RawJsonb` values using the total ordering.
/// This implementation leverages the `PartialOrd` implementation, returning `Ordering::Equal` for incomparable values.
impl Ord for RawJsonb<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ordering) => ordering,
            None => Ordering::Equal,
        }
    }
}

// Different types of values have different levels and are definitely not equal
pub(crate) fn jentry_compare_level(jentry: &JEntry) -> u8 {
    match jentry.type_code {
        NULL_TAG => NULL_LEVEL,
        CONTAINER_TAG => OBJECT_LEVEL,
        STRING_TAG => STRING_LEVEL,
        NUMBER_TAG => NUMBER_LEVEL,
        TRUE_TAG => TRUE_LEVEL,
        FALSE_TAG => FALSE_LEVEL,
        _ => INVALID_LEVEL,
    }
}

// `Scalar` values compare as the following order
// Null > Container(Array > Object) > String > Number > Boolean
fn compare_scalar(
    left_jentry: &JEntry,
    left: &[u8],
    right_jentry: &JEntry,
    right: &[u8],
) -> Option<Ordering> {
    let left_level = jentry_compare_level(left_jentry);
    let right_level = jentry_compare_level(right_jentry);
    if left_level != right_level {
        return Some(left_level.cmp(&right_level));
    }

    match (left_jentry.type_code, right_jentry.type_code) {
        (NULL_TAG, NULL_TAG) => Some(Ordering::Equal),
        (CONTAINER_TAG, CONTAINER_TAG) => compare_container(left, right),
        (STRING_TAG, STRING_TAG) => {
            let left_offset = left_jentry.length as usize;
            let left_str = unsafe { std::str::from_utf8_unchecked(&left[..left_offset]) };
            let right_offset = right_jentry.length as usize;
            let right_str = unsafe { std::str::from_utf8_unchecked(&right[..right_offset]) };
            Some(left_str.cmp(right_str))
        }
        (NUMBER_TAG, NUMBER_TAG) => {
            let left_offset = left_jentry.length as usize;
            let left_num = Number::decode(&left[..left_offset]).ok()?;
            let right_offset = right_jentry.length as usize;
            let right_num = Number::decode(&right[..right_offset]).ok()?;
            Some(left_num.cmp(&right_num))
        }
        (TRUE_TAG, TRUE_TAG) => Some(Ordering::Equal),
        (FALSE_TAG, FALSE_TAG) => Some(Ordering::Equal),
        (_, _) => None,
    }
}

fn compare_container(left: &[u8], right: &[u8]) -> Option<Ordering> {
    let left_header = read_u32(left, 0).ok()?;
    let right_header = read_u32(right, 0).ok()?;

    match (
        left_header & CONTAINER_HEADER_TYPE_MASK,
        right_header & CONTAINER_HEADER_TYPE_MASK,
    ) {
        (ARRAY_CONTAINER_TAG, ARRAY_CONTAINER_TAG) => {
            compare_array(left_header, &left[4..], right_header, &right[4..])
        }
        (OBJECT_CONTAINER_TAG, OBJECT_CONTAINER_TAG) => {
            compare_object(left_header, &left[4..], right_header, &right[4..])
        }
        (ARRAY_CONTAINER_TAG, OBJECT_CONTAINER_TAG) => Some(Ordering::Greater),
        (OBJECT_CONTAINER_TAG, ARRAY_CONTAINER_TAG) => Some(Ordering::Less),
        (_, _) => None,
    }
}

// `Array` values compares each element in turn.
fn compare_array(
    left_header: u32,
    left: &[u8],
    right_header: u32,
    right: &[u8],
) -> Option<Ordering> {
    let left_length = (left_header & CONTAINER_HEADER_LEN_MASK) as usize;
    let right_length = (right_header & CONTAINER_HEADER_LEN_MASK) as usize;

    let mut jentry_offset = 0;
    let mut left_val_offset = 4 * left_length;
    let mut right_val_offset = 4 * right_length;
    let length = if left_length <= right_length {
        left_length
    } else {
        right_length
    };
    for _ in 0..length {
        let left_encoded = read_u32(left, jentry_offset).ok()?;
        let left_jentry = JEntry::decode_jentry(left_encoded);
        let right_encoded = read_u32(right, jentry_offset).ok()?;
        let right_jentry = JEntry::decode_jentry(right_encoded);

        let order = compare_scalar(
            &left_jentry,
            &left[left_val_offset..],
            &right_jentry,
            &right[right_val_offset..],
        )?;
        if order != Ordering::Equal {
            return Some(order);
        }
        jentry_offset += 4;

        left_val_offset += left_jentry.length as usize;
        right_val_offset += right_jentry.length as usize;
    }

    Some(left_length.cmp(&right_length))
}

// `Object` values compares each key-value in turn,
// first compare the key, and then compare the value if the key is equal.
// The larger the key/value, the larger the `Object`.
fn compare_object(
    left_header: u32,
    left: &[u8],
    right_header: u32,
    right: &[u8],
) -> Option<Ordering> {
    let left_length = (left_header & CONTAINER_HEADER_LEN_MASK) as usize;
    let right_length = (right_header & CONTAINER_HEADER_LEN_MASK) as usize;

    let mut left_jentry_offset = 0;
    let mut left_val_offset = 8 * left_length;
    let mut right_jentry_offset = 0;
    let mut right_val_offset = 8 * right_length;

    // read all left key jentries and right key jentries first.
    // Note: since the values are stored after the keys,
    // we must first read all the key jentries to get the correct value offset.
    let mut left_key_jentries: VecDeque<JEntry> = VecDeque::with_capacity(left_length);
    let mut right_key_jentries: VecDeque<JEntry> = VecDeque::with_capacity(right_length);
    for _ in 0..left_length {
        let left_encoded = read_u32(left, left_jentry_offset).ok()?;
        let left_key_jentry = JEntry::decode_jentry(left_encoded);

        left_jentry_offset += 4;
        left_val_offset += left_key_jentry.length as usize;
        left_key_jentries.push_back(left_key_jentry);
    }
    for _ in 0..right_length {
        let right_encoded = read_u32(right, right_jentry_offset).ok()?;
        let right_key_jentry = JEntry::decode_jentry(right_encoded);

        right_jentry_offset += 4;
        right_val_offset += right_key_jentry.length as usize;
        right_key_jentries.push_back(right_key_jentry);
    }

    let length = if left_length <= right_length {
        left_length
    } else {
        right_length
    };

    let mut left_key_offset = 8 * left_length;
    let mut right_key_offset = 8 * right_length;
    for _ in 0..length {
        // first compare key, if keys are equal, then compare the value
        let left_key_jentry = left_key_jentries.pop_front().unwrap();
        let right_key_jentry = right_key_jentries.pop_front().unwrap();

        let key_order = compare_scalar(
            &left_key_jentry,
            &left[left_key_offset..],
            &right_key_jentry,
            &right[right_key_offset..],
        )?;
        if key_order != Ordering::Equal {
            return Some(key_order);
        }

        let left_encoded = read_u32(left, left_jentry_offset).ok()?;
        let left_val_jentry = JEntry::decode_jentry(left_encoded);
        let right_encoded = read_u32(right, right_jentry_offset).ok()?;
        let right_val_jentry = JEntry::decode_jentry(right_encoded);

        let val_order = compare_scalar(
            &left_val_jentry,
            &left[left_val_offset..],
            &right_val_jentry,
            &right[right_val_offset..],
        )?;
        if val_order != Ordering::Equal {
            return Some(val_order);
        }
        left_jentry_offset += 4;
        right_jentry_offset += 4;

        left_key_offset += left_key_jentry.length as usize;
        right_key_offset += right_key_jentry.length as usize;
        left_val_offset += left_val_jentry.length as usize;
        right_val_offset += right_val_jentry.length as usize;
    }

    Some(left_length.cmp(&right_length))
}

pub(crate) fn read_u32(buf: &[u8], idx: usize) -> Result<u32> {
    let bytes: [u8; 4] = buf
        .get(idx..idx + 4)
        .ok_or(Error::InvalidEOF)?
        .try_into()
        .unwrap();
    Ok(u32::from_be_bytes(bytes))
}
