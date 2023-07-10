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

use core::convert::TryInto;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::VecDeque;

use crate::constants::*;
use crate::error::*;
use crate::jentry::JEntry;
use crate::jsonpath::JsonPath;
use crate::jsonpath::Mode;
use crate::jsonpath::Selector;
use crate::number::Number;
use crate::parser::parse_value;
use crate::value::Object;
use crate::value::Value;
use rand::distributions::Alphanumeric;
use rand::distributions::DistString;
use rand::thread_rng;
use rand::Rng;

// builtin functions for `JSONB` bytes and `JSON` strings without decode all Values.
// The input value must be valid `JSONB' or `JSON`.

/// Build `JSONB` array from items.
/// Assuming that the input values is valid JSONB data.
pub fn build_array<'a>(
    items: impl IntoIterator<Item = &'a [u8]>,
    buf: &mut Vec<u8>,
) -> Result<(), Error> {
    let start = buf.len();
    // reserve space for header
    buf.resize(start + 4, 0);
    let mut len: u32 = 0;
    let mut data = Vec::new();
    for value in items.into_iter() {
        let header = read_u32(value, 0)?;
        let encoded_jentry = match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let jentry = &value[4..8];
                data.extend_from_slice(&value[8..]);
                jentry.try_into().unwrap()
            }
            ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG => {
                data.extend_from_slice(value);
                (CONTAINER_TAG | value.len() as u32).to_be_bytes()
            }
            _ => return Err(Error::InvalidJsonbHeader),
        };
        len += 1;
        buf.extend_from_slice(&encoded_jentry);
    }
    // write header
    let header = ARRAY_CONTAINER_TAG | len;
    for (i, b) in header.to_be_bytes().iter().enumerate() {
        buf[start + i] = *b;
    }
    buf.extend_from_slice(&data);

    Ok(())
}

/// Build `JSONB` object from items.
/// Assuming that the input values is valid JSONB data.
pub fn build_object<'a, K: AsRef<str>>(
    items: impl IntoIterator<Item = (K, &'a [u8])>,
    buf: &mut Vec<u8>,
) -> Result<(), Error> {
    let start = buf.len();
    // reserve space for header
    buf.resize(start + 4, 0);
    let mut len: u32 = 0;
    let mut key_data = Vec::new();
    let mut val_data = Vec::new();
    let mut val_jentries = VecDeque::new();
    for (key, value) in items.into_iter() {
        let key = key.as_ref();
        // write key jentry and key data
        let encoded_key_jentry = (STRING_TAG | key.len() as u32).to_be_bytes();
        buf.extend_from_slice(&encoded_key_jentry);
        key_data.extend_from_slice(key.as_bytes());

        // build value jentry and write value data
        let header = read_u32(value, 0)?;
        let encoded_val_jentry = match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let jentry = &value[4..8];
                val_data.extend_from_slice(&value[8..]);
                jentry.try_into().unwrap()
            }
            ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG => {
                val_data.extend_from_slice(value);
                (CONTAINER_TAG | value.len() as u32).to_be_bytes()
            }
            _ => return Err(Error::InvalidJsonbHeader),
        };
        val_jentries.push_back(encoded_val_jentry);
        len += 1;
    }
    // write header and value jentry
    let header = OBJECT_CONTAINER_TAG | len;
    for (i, b) in header.to_be_bytes().iter().enumerate() {
        buf[start + i] = *b;
    }
    while let Some(val_jentry) = val_jentries.pop_front() {
        buf.extend_from_slice(&val_jentry);
    }
    // write key data and value data
    buf.extend_from_slice(&key_data);
    buf.extend_from_slice(&val_data);

    Ok(())
}

/// Get the length of `JSONB` array.
pub fn array_length(value: &[u8]) -> Option<usize> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => val.array_length(),
            Err(_) => None,
        };
    }
    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        ARRAY_CONTAINER_TAG => {
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            Some(length)
        }
        _ => None,
    }
}

/// Get the inner elements of `JSONB` value by JSON path.
/// The return value may contains multiple matching elements.
pub fn get_by_path<'a>(
    value: &'a [u8],
    json_path: JsonPath<'a>,
    data: &mut Vec<u8>,
    offsets: &mut Vec<u64>,
) {
    let selector = Selector::new(json_path, Mode::Mixed);
    if !is_jsonb(value) {
        if let Ok(val) = parse_value(value) {
            let value = val.to_vec();
            selector.select(value.as_slice(), data, offsets)
        }
    } else {
        selector.select(value, data, offsets)
    }
}

/// Get the inner element of `JSONB` value by JSON path.
/// If there are multiple matching elements, only the first one is returned
pub fn get_by_path_first<'a>(
    value: &'a [u8],
    json_path: JsonPath<'a>,
    data: &mut Vec<u8>,
    offsets: &mut Vec<u64>,
) {
    let selector = Selector::new(json_path, Mode::First);
    if !is_jsonb(value) {
        if let Ok(val) = parse_value(value) {
            let value = val.to_vec();
            selector.select(value.as_slice(), data, offsets)
        }
    } else {
        selector.select(value, data, offsets)
    }
}

/// Get the inner elements of `JSONB` value by JSON path.
/// If there are multiple matching elements, return an `JSONB` Array.
pub fn get_by_path_array<'a>(
    value: &'a [u8],
    json_path: JsonPath<'a>,
    data: &mut Vec<u8>,
    offsets: &mut Vec<u64>,
) {
    let selector = Selector::new(json_path, Mode::Array);
    if !is_jsonb(value) {
        if let Ok(val) = parse_value(value) {
            let value = val.to_vec();
            selector.select(value.as_slice(), data, offsets)
        }
    } else {
        selector.select(value, data, offsets)
    }
}

/// Get the inner element of `JSONB` Array by index.
pub fn get_by_index(value: &[u8], index: usize) -> Option<Vec<u8>> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => match val {
                Value::Array(vals) => vals.get(index).map(|v| v.to_vec()),
                _ => None,
            },
            Err(_) => None,
        };
    }

    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        ARRAY_CONTAINER_TAG => {
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            if index >= length {
                return None;
            }
            let mut jentry_offset = 4;
            let mut val_offset = 4 * length + 4;
            for i in 0..length {
                let encoded = read_u32(value, jentry_offset).unwrap();
                let jentry = JEntry::decode_jentry(encoded);
                let val_length = jentry.length as usize;
                if i < index {
                    jentry_offset += 4;
                    val_offset += val_length;
                    continue;
                }
                let val = match jentry.type_code {
                    CONTAINER_TAG => value[val_offset..val_offset + val_length].to_vec(),
                    _ => {
                        let mut buf = Vec::with_capacity(8 + val_length);
                        buf.extend_from_slice(&SCALAR_CONTAINER_TAG.to_be_bytes());
                        buf.extend_from_slice(&encoded.to_be_bytes());
                        if jentry.length > 0 {
                            buf.extend_from_slice(&value[val_offset..val_offset + val_length]);
                        }
                        buf
                    }
                };
                return Some(val);
            }
            None
        }
        _ => None,
    }
}

/// Get the inner element of `JSONB` Object by key name,
/// if `ignore_case` is true, enables case-insensitive matching.
pub fn get_by_name(value: &[u8], name: &str, ignore_case: bool) -> Option<Vec<u8>> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => {
                if ignore_case {
                    val.get_by_name_ignore_case(name).map(Value::to_vec)
                } else {
                    match val {
                        Value::Object(obj) => obj.get(name).map(|v| v.to_vec()),
                        _ => None,
                    }
                }
            }
            Err(_) => None,
        };
    }

    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        OBJECT_CONTAINER_TAG => {
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            let mut jentry_offset = 4;
            let mut val_offset = 8 * length + 4;

            let mut key_jentries: VecDeque<JEntry> = VecDeque::with_capacity(length);
            for _ in 0..length {
                let encoded = read_u32(value, jentry_offset).unwrap();
                let key_jentry = JEntry::decode_jentry(encoded);

                jentry_offset += 4;
                val_offset += key_jentry.length as usize;
                key_jentries.push_back(key_jentry);
            }

            let mut offsets = None;
            let mut key_offset = 8 * length + 4;
            while let Some(key_jentry) = key_jentries.pop_front() {
                let prev_key_offset = key_offset;
                key_offset += key_jentry.length as usize;
                let key =
                    unsafe { std::str::from_utf8_unchecked(&value[prev_key_offset..key_offset]) };
                // first match the value with the same name, if not found,
                // then match the value with the ignoring case name.
                if name.eq(key) {
                    offsets = Some((jentry_offset, val_offset));
                    break;
                } else if ignore_case && name.eq_ignore_ascii_case(key) && offsets.is_none() {
                    offsets = Some((jentry_offset, val_offset));
                }
                let val_encoded = read_u32(value, jentry_offset).unwrap();
                let val_jentry = JEntry::decode_jentry(val_encoded);
                jentry_offset += 4;
                val_offset += val_jentry.length as usize;
            }
            if let Some((jentry_offset, val_offset)) = offsets {
                let encoded = read_u32(value, jentry_offset).unwrap();
                let jentry = JEntry::decode_jentry(encoded);
                let val_length = jentry.length as usize;
                let val = match jentry.type_code {
                    CONTAINER_TAG => value[val_offset..val_offset + val_length].to_vec(),
                    _ => {
                        let mut buf: Vec<u8> = Vec::with_capacity(val_length + 8);
                        let scalar_header = SCALAR_CONTAINER_TAG;
                        buf.extend_from_slice(&scalar_header.to_be_bytes());
                        buf.extend_from_slice(&encoded.to_be_bytes());
                        if val_length > 0 {
                            buf.extend_from_slice(&value[val_offset..val_offset + val_length]);
                        }
                        buf
                    }
                };
                return Some(val);
            }
            None
        }
        _ => None,
    }
}

/// Get the keys of a `JSONB` object.
pub fn object_keys(value: &[u8]) -> Option<Vec<u8>> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => val.object_keys().map(|val| val.to_vec()),
            Err(_) => None,
        };
    }

    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        OBJECT_CONTAINER_TAG => {
            let mut buf: Vec<u8> = Vec::new();
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            let key_header = ARRAY_CONTAINER_TAG | length as u32;
            buf.extend_from_slice(&key_header.to_be_bytes());

            let mut jentry_offset = 4;
            let mut key_offset = 8 * length + 4;
            let mut key_offsets = Vec::with_capacity(length);
            for _ in 0..length {
                let key_encoded = read_u32(value, jentry_offset).unwrap();
                let key_jentry = JEntry::decode_jentry(key_encoded);
                buf.extend_from_slice(&key_encoded.to_be_bytes());

                jentry_offset += 4;
                key_offset += key_jentry.length as usize;
                key_offsets.push(key_offset);
            }
            let mut prev_key_offset = 8 * length + 4;
            for key_offset in key_offsets {
                if key_offset > prev_key_offset {
                    buf.extend_from_slice(&value[prev_key_offset..key_offset]);
                }
                prev_key_offset = key_offset;
            }
            Some(buf)
        }
        _ => None,
    }
}

/// Convert the values of a `JSONB` array to vector.
pub fn array_values(value: &[u8]) -> Option<Vec<Vec<u8>>> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => match val {
                Value::Array(vals) => {
                    Some(vals.into_iter().map(|val| val.to_vec()).collect::<Vec<_>>())
                }
                _ => None,
            },
            Err(_) => None,
        };
    }

    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        ARRAY_CONTAINER_TAG => {
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            let mut jentry_offset = 4;
            let mut val_offset = 4 * length + 4;
            let mut items = Vec::with_capacity(length);
            for _ in 0..length {
                let encoded = read_u32(value, jentry_offset).unwrap();
                let jentry = JEntry::decode_jentry(encoded);
                let val_length = jentry.length as usize;
                let item = match jentry.type_code {
                    CONTAINER_TAG => value[val_offset..val_offset + val_length].to_vec(),
                    _ => {
                        let mut buf = Vec::with_capacity(8 + val_length);
                        buf.extend_from_slice(&SCALAR_CONTAINER_TAG.to_be_bytes());
                        buf.extend_from_slice(&encoded.to_be_bytes());
                        if jentry.length > 0 {
                            buf.extend_from_slice(&value[val_offset..val_offset + val_length]);
                        }
                        buf
                    }
                };
                items.push(item);

                jentry_offset += 4;
                val_offset += val_length;
            }
            Some(items)
        }
        _ => None,
    }
}

/// `JSONB` values supports partial decode for comparison,
/// if the values are found to be unequal, the result will be returned immediately.
/// In first level header, values compare as the following order:
/// Scalar Null > Array > Object > Other Scalars(String > Number > Boolean).
pub fn compare(left: &[u8], right: &[u8]) -> Result<Ordering, Error> {
    if !is_jsonb(left) && !is_jsonb(right) {
        let lres = parse_value(left);
        let rres = parse_value(right);
        match (lres, rres) {
            (Ok(lval), Ok(rval)) => {
                let lbuf = lval.to_vec();
                let rbuf = rval.to_vec();
                return compare(&lbuf, &rbuf);
            }
            (Ok(_), Err(_)) => {
                return Ok(Ordering::Greater);
            }
            (Err(_), Ok(_)) => {
                return Ok(Ordering::Less);
            }
            (Err(_), Err(_)) => {
                return Ok(left.cmp(right));
            }
        }
    } else if !is_jsonb(left) {
        match parse_value(left) {
            Ok(lval) => {
                let lbuf = lval.to_vec();
                return compare(&lbuf, right);
            }
            Err(_) => {
                return Ok(Ordering::Less);
            }
        }
    } else if !is_jsonb(right) {
        match parse_value(right) {
            Ok(rval) => {
                let rbuf = rval.to_vec();
                return compare(left, &rbuf);
            }
            Err(_) => {
                return Ok(Ordering::Greater);
            }
        }
    }

    let left_header = read_u32(left, 0)?;
    let right_header = read_u32(right, 0)?;
    match (
        left_header & CONTAINER_HEADER_TYPE_MASK,
        right_header & CONTAINER_HEADER_TYPE_MASK,
    ) {
        (SCALAR_CONTAINER_TAG, SCALAR_CONTAINER_TAG) => {
            let left_encoded = read_u32(left, 4)?;
            let left_jentry = JEntry::decode_jentry(left_encoded);
            let right_encoded = read_u32(right, 4)?;
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
            let left_encoded = read_u32(left, 4)?;
            let left_jentry = JEntry::decode_jentry(left_encoded);
            match left_jentry.type_code {
                NULL_TAG => Ok(Ordering::Greater),
                _ => Ok(Ordering::Less),
            }
        }
        (ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG, SCALAR_CONTAINER_TAG) => {
            let right_encoded = read_u32(right, 4)?;
            let right_jentry = JEntry::decode_jentry(right_encoded);
            match right_jentry.type_code {
                NULL_TAG => Ok(Ordering::Less),
                _ => Ok(Ordering::Greater),
            }
        }
        (ARRAY_CONTAINER_TAG, OBJECT_CONTAINER_TAG) => Ok(Ordering::Greater),
        (OBJECT_CONTAINER_TAG, ARRAY_CONTAINER_TAG) => Ok(Ordering::Less),
        (_, _) => Err(Error::InvalidJsonbHeader),
    }
}

// Different types of values have different levels and are definitely not equal
fn jentry_compare_level(jentry: &JEntry) -> u8 {
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
) -> Result<Ordering, Error> {
    let left_level = jentry_compare_level(left_jentry);
    let right_level = jentry_compare_level(right_jentry);
    if left_level != right_level {
        return Ok(left_level.cmp(&right_level));
    }

    match (left_jentry.type_code, right_jentry.type_code) {
        (NULL_TAG, NULL_TAG) => Ok(Ordering::Equal),
        (CONTAINER_TAG, CONTAINER_TAG) => compare_container(left, right),
        (STRING_TAG, STRING_TAG) => {
            let left_offset = left_jentry.length as usize;
            let left_str = unsafe { std::str::from_utf8_unchecked(&left[..left_offset]) };
            let right_offset = right_jentry.length as usize;
            let right_str = unsafe { std::str::from_utf8_unchecked(&right[..right_offset]) };
            Ok(left_str.cmp(right_str))
        }
        (NUMBER_TAG, NUMBER_TAG) => {
            let left_offset = left_jentry.length as usize;
            let left_num = Number::decode(&left[..left_offset]);
            let right_offset = right_jentry.length as usize;
            let right_num = Number::decode(&right[..right_offset]);
            Ok(left_num.cmp(&right_num))
        }
        (TRUE_TAG, TRUE_TAG) => Ok(Ordering::Equal),
        (FALSE_TAG, FALSE_TAG) => Ok(Ordering::Equal),
        (_, _) => Err(Error::InvalidJsonbJEntry),
    }
}

fn compare_container(left: &[u8], right: &[u8]) -> Result<Ordering, Error> {
    let left_header = read_u32(left, 0)?;
    let right_header = read_u32(right, 0)?;

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
        (ARRAY_CONTAINER_TAG, OBJECT_CONTAINER_TAG) => Ok(Ordering::Greater),
        (OBJECT_CONTAINER_TAG, ARRAY_CONTAINER_TAG) => Ok(Ordering::Less),
        (_, _) => Err(Error::InvalidJsonbHeader),
    }
}

// `Array` values compares each element in turn.
fn compare_array(
    left_header: u32,
    left: &[u8],
    right_header: u32,
    right: &[u8],
) -> Result<Ordering, Error> {
    let left_length = (left_header & CONTAINER_HEADER_LEN_MASK) as usize;
    let right_length = (right_header & CONTAINER_HEADER_LEN_MASK) as usize;

    let mut jentry_offset = 0;
    let mut left_val_offset = 4 * left_length;
    let mut right_val_offset = 4 * right_length;
    let length = if left_length < right_length {
        left_length
    } else {
        right_length
    };
    for _ in 0..length {
        let left_encoded = read_u32(left, jentry_offset)?;
        let left_jentry = JEntry::decode_jentry(left_encoded);
        let right_encoded = read_u32(right, jentry_offset)?;
        let right_jentry = JEntry::decode_jentry(right_encoded);

        let order = compare_scalar(
            &left_jentry,
            &left[left_val_offset..],
            &right_jentry,
            &right[right_val_offset..],
        )?;
        if order != Ordering::Equal {
            return Ok(order);
        }
        jentry_offset += 4;

        left_val_offset += left_jentry.length as usize;
        right_val_offset += right_jentry.length as usize;
    }

    Ok(left_length.cmp(&right_length))
}

// `Object` values compares each key-value in turn,
// first compare the key, and then compare the value if the key is equal.
// The larger the key/value, the larger the `Object`.
fn compare_object(
    left_header: u32,
    left: &[u8],
    right_header: u32,
    right: &[u8],
) -> Result<Ordering, Error> {
    let left_length = (left_header & CONTAINER_HEADER_LEN_MASK) as usize;
    let right_length = (right_header & CONTAINER_HEADER_LEN_MASK) as usize;

    let mut jentry_offset = 0;
    let mut left_val_offset = 8 * left_length;
    let mut right_val_offset = 8 * right_length;

    let length = if left_length < right_length {
        left_length
    } else {
        right_length
    };
    // read all key jentries first
    let mut left_key_jentries: VecDeque<JEntry> = VecDeque::with_capacity(length);
    let mut right_key_jentries: VecDeque<JEntry> = VecDeque::with_capacity(length);
    for _ in 0..length {
        let left_encoded = read_u32(left, jentry_offset)?;
        let left_key_jentry = JEntry::decode_jentry(left_encoded);
        let right_encoded = read_u32(right, jentry_offset)?;
        let right_key_jentry = JEntry::decode_jentry(right_encoded);

        jentry_offset += 4;
        left_val_offset += left_key_jentry.length as usize;
        right_val_offset += right_key_jentry.length as usize;

        left_key_jentries.push_back(left_key_jentry);
        right_key_jentries.push_back(right_key_jentry);
    }

    let mut left_jentry_offset = 4 * left_length;
    let mut right_jentry_offset = 4 * right_length;
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
            return Ok(key_order);
        }

        let left_encoded = read_u32(left, left_jentry_offset)?;
        let left_val_jentry = JEntry::decode_jentry(left_encoded);
        let right_encoded = read_u32(right, right_jentry_offset)?;
        let right_val_jentry = JEntry::decode_jentry(right_encoded);

        let val_order = compare_scalar(
            &left_val_jentry,
            &left[left_val_offset..],
            &right_val_jentry,
            &right[right_val_offset..],
        )?;
        if val_order != Ordering::Equal {
            return Ok(val_order);
        }
        left_jentry_offset += 4;
        right_jentry_offset += 4;

        left_key_offset += left_key_jentry.length as usize;
        right_key_offset += right_key_jentry.length as usize;
        left_val_offset += left_val_jentry.length as usize;
        right_val_offset += right_val_jentry.length as usize;
    }

    Ok(left_length.cmp(&right_length))
}

/// Returns true if the `JSONB` is a Null.
pub fn is_null(value: &[u8]) -> bool {
    as_null(value).is_some()
}

/// If the `JSONB` is a Null, returns (). Returns None otherwise.
pub fn as_null(value: &[u8]) -> Option<()> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => val.as_null(),
            Err(_) => None,
        };
    }
    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        SCALAR_CONTAINER_TAG => {
            let jentry = read_u32(value, 4).unwrap();
            match jentry {
                NULL_TAG => Some(()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Returns true if the `JSONB` is a Boolean. Returns false otherwise.
pub fn is_boolean(value: &[u8]) -> bool {
    as_bool(value).is_some()
}

/// If the `JSONB` is a Boolean, returns the associated bool. Returns None otherwise.
pub fn as_bool(value: &[u8]) -> Option<bool> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => val.as_bool(),
            Err(_) => None,
        };
    }
    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        SCALAR_CONTAINER_TAG => {
            let jentry = read_u32(value, 4).unwrap();
            match jentry {
                FALSE_TAG => Some(false),
                TRUE_TAG => Some(true),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Cast `JSONB` value to Boolean
pub fn to_bool(value: &[u8]) -> Result<bool, Error> {
    if let Some(v) = as_bool(value) {
        return Ok(v);
    } else if let Some(v) = as_str(value) {
        if &v.to_lowercase() == "true" {
            return Ok(true);
        } else if &v.to_lowercase() == "false" {
            return Ok(false);
        }
    }
    Err(Error::InvalidCast)
}

/// Returns true if the `JSONB` is a Number. Returns false otherwise.
pub fn is_number(value: &[u8]) -> bool {
    as_number(value).is_some()
}

/// If the `JSONB` is a Number, returns the Number. Returns None otherwise.
pub fn as_number(value: &[u8]) -> Option<Number> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => val.as_number().cloned(),
            Err(_) => None,
        };
    }
    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        SCALAR_CONTAINER_TAG => {
            let jentry_encoded = read_u32(value, 4).unwrap();
            let jentry = JEntry::decode_jentry(jentry_encoded);
            match jentry.type_code {
                NUMBER_TAG => {
                    let length = jentry.length as usize;
                    let num = Number::decode(&value[8..8 + length]);
                    Some(num)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Returns true if the `JSONB` is a i64 Number. Returns false otherwise.
pub fn is_i64(value: &[u8]) -> bool {
    as_i64(value).is_some()
}

/// Cast `JSONB` value to i64
pub fn to_i64(value: &[u8]) -> Result<i64, Error> {
    if let Some(v) = as_i64(value) {
        return Ok(v);
    } else if let Some(v) = as_bool(value) {
        if v {
            return Ok(1_i64);
        } else {
            return Ok(0_i64);
        }
    } else if let Some(v) = as_str(value) {
        if let Ok(v) = v.parse::<i64>() {
            return Ok(v);
        }
    }
    Err(Error::InvalidCast)
}

/// If the `JSONB` is a Number, represent it as i64 if possible. Returns None otherwise.
pub fn as_i64(value: &[u8]) -> Option<i64> {
    match as_number(value) {
        Some(num) => num.as_i64(),
        None => None,
    }
}

/// Returns true if the `JSONB` is a u64 Number. Returns false otherwise.
pub fn is_u64(value: &[u8]) -> bool {
    as_u64(value).is_some()
}

/// If the `JSONB` is a Number, represent it as u64 if possible. Returns None otherwise.
pub fn as_u64(value: &[u8]) -> Option<u64> {
    match as_number(value) {
        Some(num) => num.as_u64(),
        None => None,
    }
}

/// Cast `JSONB` value to u64
pub fn to_u64(value: &[u8]) -> Result<u64, Error> {
    if let Some(v) = as_u64(value) {
        return Ok(v);
    } else if let Some(v) = as_bool(value) {
        if v {
            return Ok(1_u64);
        } else {
            return Ok(0_u64);
        }
    } else if let Some(v) = as_str(value) {
        if let Ok(v) = v.parse::<u64>() {
            return Ok(v);
        }
    }
    Err(Error::InvalidCast)
}

/// Returns true if the `JSONB` is a f64 Number. Returns false otherwise.
pub fn is_f64(value: &[u8]) -> bool {
    as_f64(value).is_some()
}

/// If the `JSONB` is a Number, represent it as f64 if possible. Returns None otherwise.
pub fn as_f64(value: &[u8]) -> Option<f64> {
    match as_number(value) {
        Some(num) => num.as_f64(),
        None => None,
    }
}

/// Cast `JSONB` value to f64
pub fn to_f64(value: &[u8]) -> Result<f64, Error> {
    if let Some(v) = as_f64(value) {
        return Ok(v);
    } else if let Some(v) = as_bool(value) {
        if v {
            return Ok(1_f64);
        } else {
            return Ok(0_f64);
        }
    } else if let Some(v) = as_str(value) {
        if let Ok(v) = v.parse::<f64>() {
            return Ok(v);
        }
    }
    Err(Error::InvalidCast)
}

/// Returns true if the `JSONB` is a String. Returns false otherwise.
pub fn is_string(value: &[u8]) -> bool {
    as_str(value).is_some()
}

/// If the `JSONB` is a String, returns the String. Returns None otherwise.
pub fn as_str(value: &[u8]) -> Option<Cow<'_, str>> {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => match val {
                Value::String(s) => Some(s.clone()),
                _ => None,
            },
            Err(_) => None,
        };
    }
    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        SCALAR_CONTAINER_TAG => {
            let jentry_encoded = read_u32(value, 4).unwrap();
            let jentry = JEntry::decode_jentry(jentry_encoded);
            match jentry.type_code {
                STRING_TAG => {
                    let length = jentry.length as usize;
                    let s = unsafe { std::str::from_utf8_unchecked(&value[8..8 + length]) };
                    Some(Cow::Borrowed(s))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Cast `JSONB` value to String
pub fn to_str(value: &[u8]) -> Result<String, Error> {
    if let Some(v) = as_str(value) {
        return Ok(v.to_string());
    } else if let Some(v) = as_bool(value) {
        if v {
            return Ok("true".to_string());
        } else {
            return Ok("false".to_string());
        }
    } else if let Some(v) = as_number(value) {
        return Ok(format!("{}", v));
    }
    Err(Error::InvalidCast)
}

/// Returns true if the `JSONB` is An Array. Returns false otherwise.
pub fn is_array(value: &[u8]) -> bool {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => val.is_array(),
            Err(_) => false,
        };
    }
    let header = read_u32(value, 0).unwrap();
    matches!(header & CONTAINER_HEADER_TYPE_MASK, ARRAY_CONTAINER_TAG)
}

/// Returns true if the `JSONB` is An Object. Returns false otherwise.
pub fn is_object(value: &[u8]) -> bool {
    if !is_jsonb(value) {
        return match parse_value(value) {
            Ok(val) => val.is_object(),
            Err(_) => false,
        };
    }
    let header = read_u32(value, 0).unwrap();
    matches!(header & CONTAINER_HEADER_TYPE_MASK, OBJECT_CONTAINER_TAG)
}

/// Convert `JSONB` value to String
pub fn to_string(value: &[u8]) -> String {
    if !is_jsonb(value) {
        return String::from_utf8_lossy(value).to_string();
    }

    let mut json = String::new();
    container_to_string(value, &mut 0, &mut json);
    json
}

fn container_to_string(value: &[u8], offset: &mut usize, json: &mut String) {
    let header = read_u32(value, *offset).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        SCALAR_CONTAINER_TAG => {
            let mut jentry_offset = 4 + *offset;
            let mut value_offset = 8 + *offset;
            scalar_to_string(value, &mut jentry_offset, &mut value_offset, json);
        }
        ARRAY_CONTAINER_TAG => {
            json.push('[');
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            let mut jentry_offset = 4 + *offset;
            let mut value_offset = 4 + *offset + 4 * length;
            for i in 0..length {
                if i > 0 {
                    json.push(',');
                }
                scalar_to_string(value, &mut jentry_offset, &mut value_offset, json);
            }
            json.push(']');
        }
        OBJECT_CONTAINER_TAG => {
            json.push('{');
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            let mut jentry_offset = 4 + *offset;
            let mut key_offset = 4 + *offset + 8 * length;
            let mut keys = VecDeque::with_capacity(length);
            for _ in 0..length {
                let jentry_encoded = read_u32(value, jentry_offset).unwrap();
                let jentry = JEntry::decode_jentry(jentry_encoded);
                let key_length = jentry.length as usize;
                keys.push_back((key_offset, key_offset + key_length));
                jentry_offset += 4;
                key_offset += key_length;
            }
            let mut value_offset = key_offset;
            for i in 0..length {
                if i > 0 {
                    json.push(',');
                }
                let (key_start, key_end) = keys.pop_front().unwrap();
                escape_scalar_string(value, key_start, key_end, json);
                json.push(':');
                scalar_to_string(value, &mut jentry_offset, &mut value_offset, json);
            }
            json.push('}');
        }
        _ => {}
    }
}

fn scalar_to_string(
    value: &[u8],
    jentry_offset: &mut usize,
    value_offset: &mut usize,
    json: &mut String,
) {
    let jentry_encoded = read_u32(value, *jentry_offset).unwrap();
    let jentry = JEntry::decode_jentry(jentry_encoded);
    let length = jentry.length as usize;
    match jentry.type_code {
        NULL_TAG => json.push_str("null"),
        TRUE_TAG => json.push_str("true"),
        FALSE_TAG => json.push_str("false"),
        NUMBER_TAG => {
            let num = Number::decode(&value[*value_offset..*value_offset + length]);
            json.push_str(&format!("{num}"));
        }
        STRING_TAG => {
            escape_scalar_string(value, *value_offset, *value_offset + length, json);
        }
        CONTAINER_TAG => {
            container_to_string(value, value_offset, json);
        }
        _ => {}
    }
    *jentry_offset += 4;
    *value_offset += length;
}

fn escape_scalar_string(value: &[u8], start: usize, end: usize, json: &mut String) {
    json.push('\"');
    let mut last_start = start;
    for i in start..end {
        // add backslash for escaped characters.
        let c = match value[i] {
            0x5C => "\\\\",
            0x22 => "\\\"",
            0x08 => "\\b",
            0x0C => "\\f",
            0x0A => "\\n",
            0x0D => "\\r",
            0x09 => "\\t",
            _ => {
                continue;
            }
        };
        if i > last_start {
            let val = String::from_utf8_lossy(&value[last_start..i]);
            json.push_str(&val);
        }
        json.push_str(c);
        last_start = i + 1;
    }
    if last_start < end {
        let val = String::from_utf8_lossy(&value[last_start..end]);
        json.push_str(&val);
    }
    json.push('\"');
}

/// Convert `JSONB` value to comparable vector.
/// The compare rules are the same as the `compare` function.
/// Scalar Null > Array > Object > Other Scalars(String > Number > Boolean).
pub fn convert_to_comparable(value: &[u8], buf: &mut Vec<u8>) {
    let depth = 0;
    if !is_jsonb(value) {
        match parse_value(value) {
            Ok(val) => {
                let val_buf = val.to_vec();
                convert_to_comparable(&val_buf, buf);
            }
            Err(_) => {
                buf.push(depth);
                buf.push(INVALID_LEVEL);
                buf.extend_from_slice(value);
            }
        }
        return;
    }
    let header = read_u32(value, 0).unwrap();
    match header & CONTAINER_HEADER_TYPE_MASK {
        SCALAR_CONTAINER_TAG => {
            let encoded = read_u32(value, 4).unwrap();
            let jentry = JEntry::decode_jentry(encoded);
            scalar_convert_to_comparable(depth, &jentry, &value[8..], buf);
        }
        ARRAY_CONTAINER_TAG => {
            buf.push(depth);
            buf.push(ARRAY_LEVEL);
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            array_convert_to_comparable(depth + 1, length, &value[4..], buf);
        }
        OBJECT_CONTAINER_TAG => {
            buf.push(depth);
            buf.push(OBJECT_LEVEL);
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            object_convert_to_comparable(depth + 1, length, &value[4..], buf);
        }
        _ => {}
    }
}

fn scalar_convert_to_comparable(depth: u8, jentry: &JEntry, value: &[u8], buf: &mut Vec<u8>) {
    buf.push(depth);
    let level = jentry_compare_level(jentry);
    match jentry.type_code {
        CONTAINER_TAG => {
            let header = read_u32(value, 0).unwrap();
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
            match header & CONTAINER_HEADER_TYPE_MASK {
                ARRAY_CONTAINER_TAG => {
                    buf.push(ARRAY_LEVEL);
                    array_convert_to_comparable(depth + 1, length, &value[4..], buf);
                }
                OBJECT_CONTAINER_TAG => {
                    buf.push(OBJECT_LEVEL);
                    object_convert_to_comparable(depth + 1, length, &value[4..], buf);
                }
                _ => {}
            }
        }
        _ => {
            buf.push(level);
            match jentry.type_code {
                STRING_TAG => {
                    let length = jentry.length as usize;
                    buf.extend_from_slice(&value[..length]);
                }
                NUMBER_TAG => {
                    let length = jentry.length as usize;
                    let num = Number::decode(&value[..length]);
                    let n = num.as_f64().unwrap();
                    // https://github.com/rust-lang/rust/blob/9c20b2a8cc7588decb6de25ac6a7912dcef24d65/library/core/src/num/f32.rs#L1176-L1260
                    let s = n.to_bits() as i64;
                    let v = s ^ (((s >> 63) as u64) >> 1) as i64;
                    let mut b = v.to_be_bytes();
                    // Toggle top "sign" bit to ensure consistent sort order
                    b[0] ^= 0x80;
                    buf.extend_from_slice(&b);
                }
                _ => {}
            }
        }
    }
}

fn array_convert_to_comparable(depth: u8, length: usize, value: &[u8], buf: &mut Vec<u8>) {
    let mut jentry_offset = 0;
    let mut val_offset = 4 * length;
    for _ in 0..length {
        let encoded = read_u32(value, jentry_offset).unwrap();
        let jentry = JEntry::decode_jentry(encoded);
        scalar_convert_to_comparable(depth, &jentry, &value[val_offset..], buf);
        jentry_offset += 4;
        val_offset += jentry.length as usize;
    }
}

fn object_convert_to_comparable(depth: u8, length: usize, value: &[u8], buf: &mut Vec<u8>) {
    let mut jentry_offset = 0;
    let mut val_offset = 8 * length;

    // read all key jentries first
    let mut key_jentries: VecDeque<JEntry> = VecDeque::with_capacity(length);
    for _ in 0..length {
        let encoded = read_u32(value, jentry_offset).unwrap();
        let key_jentry = JEntry::decode_jentry(encoded);

        jentry_offset += 4;
        val_offset += key_jentry.length as usize;
        key_jentries.push_back(key_jentry);
    }

    let mut key_offset = 8 * length;
    for _ in 0..length {
        let key_jentry = key_jentries.pop_front().unwrap();
        scalar_convert_to_comparable(depth, &key_jentry, &value[key_offset..], buf);

        let encoded = read_u32(value, jentry_offset).unwrap();
        let val_jentry = JEntry::decode_jentry(encoded);
        scalar_convert_to_comparable(depth, &val_jentry, &value[val_offset..], buf);

        jentry_offset += 4;
        key_offset += key_jentry.length as usize;
        val_offset += val_jentry.length as usize;
    }
}

/// generate random JSONB value
pub fn rand_value() -> Value<'static> {
    let mut rng = thread_rng();
    let val = match rng.gen_range(0..=2) {
        0 => {
            let len = rng.gen_range(0..=5);
            let mut values = Vec::with_capacity(len);
            for _ in 0..len {
                values.push(rand_scalar_value());
            }
            Value::Array(values)
        }
        1 => {
            let len = rng.gen_range(0..=5);
            let mut obj = Object::new();
            for _ in 0..len {
                let k = Alphanumeric.sample_string(&mut rng, 5);
                let v = rand_scalar_value();
                obj.insert(k, v);
            }
            Value::Object(obj)
        }
        _ => rand_scalar_value(),
    };
    val
}

fn rand_scalar_value() -> Value<'static> {
    let mut rng = thread_rng();
    let val = match rng.gen_range(0..=3) {
        0 => {
            let v = rng.gen_bool(0.5);
            Value::Bool(v)
        }
        1 => {
            let s = Alphanumeric.sample_string(&mut rng, 5);
            Value::String(Cow::from(s))
        }
        2 => match rng.gen_range(0..=2) {
            0 => {
                let n: u64 = rng.gen_range(0..=100000);
                Value::Number(Number::UInt64(n))
            }
            1 => {
                let n: i64 = rng.gen_range(-100000..=100000);
                Value::Number(Number::Int64(n))
            }
            _ => {
                let n: f64 = rng.gen_range(-4000.0..1.3e5);
                Value::Number(Number::Float64(n))
            }
        },
        _ => Value::Null,
    };
    val
}

// Check whether the value is `JSONB` format,
// for compatibility with previous `JSON` string.
fn is_jsonb(value: &[u8]) -> bool {
    if let Some(v) = value.first() {
        if matches!(*v, ARRAY_PREFIX | OBJECT_PREFIX | SCALAR_PREFIX) {
            return true;
        }
    }
    false
}

fn read_u32(buf: &[u8], idx: usize) -> Result<u32, Error> {
    let bytes: [u8; 4] = buf
        .get(idx..idx + 4)
        .ok_or(Error::InvalidEOF)?
        .try_into()
        .unwrap();
    Ok(u32::from_be_bytes(bytes))
}
