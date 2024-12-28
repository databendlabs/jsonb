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
use crate::iterator::iterate_array;
use crate::iterator::iterate_object_entries;
use crate::jentry::JEntry;
use crate::number::Number;
use crate::parser::parse_value;

use crate::RawJsonb;

impl RawJsonb<'_> {
    /// Converts a JSONB value to a serde_json::Value.
    ///
    /// This function converts a JSONB value into a `serde_json::Value`.  This allows you to use the powerful features of the `serde_json` crate for further manipulation and processing of the data.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(serde_json::Value)` - The `serde_json::Value` representation of the JSONB data.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use serde_json::json;
    ///
    /// // Convert a JSONB object
    /// let obj_jsonb = r#"{"a": 1, "b": "hello"}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let serde_value = raw_jsonb.to_serde_json().unwrap();
    /// assert_eq!(serde_value, json!({"a": 1, "b": "hello"}));
    ///
    /// // Convert a JSONB array
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let serde_value = raw_jsonb.to_serde_json().unwrap();
    /// assert_eq!(serde_value, json!([1, 2, 3]));
    ///
    /// // Convert a JSONB scalar
    /// let num_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = num_jsonb.as_raw();
    /// let serde_value = raw_jsonb.to_serde_json().unwrap();
    /// assert_eq!(serde_value, json!(123));
    ///
    /// // Invalid JSONB data
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.to_serde_json();
    /// assert!(result.is_err());
    /// ```
    pub fn to_serde_json(&self) -> Result<serde_json::Value, Error> {
        let value = self.data;
        Self::containter_to_serde_json(value)
    }

    /// Converts a JSONB value to a serde_json::Map (if it's a JSON object).
    ///
    /// This function attempts to convert a JSONB value into a `serde_json::Map<String, serde_json::Value>`.  If the JSONB value is a JSON object, the function returns `Some` containing the converted map; otherwise, it returns `None`. This allows using the powerful features of the `serde_json` crate for further manipulation and processing of the object data.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(serde_json::Map<String, serde_json::Value>))` - If the value is a JSON object, the converted map.
    /// * `Ok(None)` - If the value is not a JSON object (e.g., array, scalar).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use serde_json::json;
    /// use serde_json::Map;
    ///
    /// // JSON object
    /// let obj_jsonb = r#"{"a": 1, "b": "hello"}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let serde_map = raw_jsonb.to_serde_json_object().unwrap();
    /// assert_eq!(serde_map, Some(json!({"a": 1, "b": "hello"}).as_object().unwrap().clone()));
    ///
    /// // Non-object values
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_serde_json_object().unwrap(), None);
    ///
    /// let num_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = num_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_serde_json_object().unwrap(), None);
    ///
    /// // Invalid JSONB data
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.to_serde_json_object();
    /// assert!(result.is_err());
    /// ```
    pub fn to_serde_json_object(
        &self,
    ) -> Result<Option<serde_json::Map<String, serde_json::Value>>, Error> {
        let value = self.data;
        Self::containter_to_serde_json_object(value)
    }

    fn containter_to_serde_json_object(
        value: &[u8],
    ) -> Result<Option<serde_json::Map<String, serde_json::Value>>, Error> {
        let header = read_u32(value, 0).unwrap_or_default();
        let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;

        let obj_value = match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {
                let mut obj = serde_json::Map::with_capacity(length);
                for (key, jentry, val) in iterate_object_entries(value, header) {
                    let item = Self::scalar_to_serde_json(jentry, val)?;
                    obj.insert(key.to_string(), item);
                }
                Some(obj)
            }
            ARRAY_CONTAINER_TAG | SCALAR_CONTAINER_TAG => None,
            _ => {
                return Err(Error::InvalidJsonb);
            }
        };
        Ok(obj_value)
    }

    fn containter_to_serde_json(value: &[u8]) -> Result<serde_json::Value, Error> {
        let header = read_u32(value, 0).unwrap_or_default();
        let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;

        let json_value = match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {
                let mut obj = serde_json::Map::with_capacity(length);
                for (key, jentry, val) in iterate_object_entries(value, header) {
                    let item = Self::scalar_to_serde_json(jentry, val)?;
                    obj.insert(key.to_string(), item);
                }
                serde_json::Value::Object(obj)
            }
            ARRAY_CONTAINER_TAG => {
                let mut arr = Vec::with_capacity(length);
                for (jentry, val) in iterate_array(value, header) {
                    let item = Self::scalar_to_serde_json(jentry, val)?;
                    arr.push(item);
                }
                serde_json::Value::Array(arr)
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = match read_u32(value, 4) {
                    Ok(encoded) => encoded,
                    Err(_) => {
                        return Err(Error::InvalidJsonb);
                    }
                };
                let jentry = JEntry::decode_jentry(encoded);
                Self::scalar_to_serde_json(jentry, &value[8..])?
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        };
        Ok(json_value)
    }

    fn scalar_to_serde_json(jentry: JEntry, value: &[u8]) -> Result<serde_json::Value, Error> {
        let json_value = match jentry.type_code {
            NULL_TAG => serde_json::Value::Null,
            TRUE_TAG => serde_json::Value::Bool(true),
            FALSE_TAG => serde_json::Value::Bool(false),
            NUMBER_TAG => {
                let len = jentry.length as usize;
                let n = Number::decode(&value[..len])?;
                match n {
                    Number::Int64(v) => serde_json::Value::Number(serde_json::Number::from(v)),
                    Number::UInt64(v) => serde_json::Value::Number(serde_json::Number::from(v)),
                    Number::Float64(v) => match serde_json::Number::from_f64(v) {
                        Some(v) => serde_json::Value::Number(v),
                        None => {
                            return Err(Error::InvalidJson);
                        }
                    },
                }
            }
            STRING_TAG => {
                let len = jentry.length as usize;
                let s = unsafe { String::from_utf8_unchecked(value[..len].to_vec()) };
                serde_json::Value::String(s)
            }
            CONTAINER_TAG => Self::containter_to_serde_json(value)?,
            _ => {
                return Err(Error::InvalidJsonb);
            }
        };
        Ok(json_value)
    }

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
    /// use jsonb::{OwnedJsonb, RawJsonb};
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
        let value = self.data;
        let mut json = String::with_capacity(value.len());
        if Self::container_to_string(value, &mut 0, &mut json, &PrettyOpts::new(false)).is_err() {
            json.clear();
            // Compatible with text json data
            match parse_value(value) {
                Ok(val) => {
                    json = format!("{}", val);
                }
                Err(_) => {
                    json.push_str("null");
                }
            }
        }
        json
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
    /// use jsonb::{OwnedJsonb, RawJsonb};
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
        let value = self.data;
        let mut json = String::with_capacity(value.len());
        if Self::container_to_string(value, &mut 0, &mut json, &PrettyOpts::new(true)).is_err() {
            json.clear();
            // Compatible with text json data
            match parse_value(value) {
                Ok(val) => {
                    let mut buf = Vec::with_capacity(value.len());
                    val.write_to_vec(&mut buf);
                    if Self::container_to_string(
                        buf.as_ref(),
                        &mut 0,
                        &mut json,
                        &PrettyOpts::new(true),
                    )
                    .is_err()
                    {
                        json.clear();
                        json.push_str("null");
                    }
                }
                Err(_) => {
                    json.push_str("null");
                }
            }
        }
        json
    }

    fn container_to_string(
        value: &[u8],
        offset: &mut usize,
        json: &mut String,
        pretty_opts: &PrettyOpts,
    ) -> Result<(), Error> {
        let header = read_u32(value, *offset)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let mut jentry_offset = 4 + *offset;
                let mut value_offset = 8 + *offset;
                Self::scalar_to_string(
                    value,
                    &mut jentry_offset,
                    &mut value_offset,
                    json,
                    pretty_opts,
                )?;
            }
            ARRAY_CONTAINER_TAG => {
                if pretty_opts.enabled {
                    json.push_str("[\n");
                } else {
                    json.push('[');
                }
                let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
                let mut jentry_offset = 4 + *offset;
                let mut value_offset = 4 + *offset + 4 * length;
                let inner_pretty_ops = pretty_opts.inc_indent();
                for i in 0..length {
                    if i > 0 {
                        if pretty_opts.enabled {
                            json.push_str(",\n");
                        } else {
                            json.push(',');
                        }
                    }
                    if pretty_opts.enabled {
                        json.push_str(&inner_pretty_ops.generate_indent());
                    }
                    Self::scalar_to_string(
                        value,
                        &mut jentry_offset,
                        &mut value_offset,
                        json,
                        &inner_pretty_ops,
                    )?;
                }
                if pretty_opts.enabled {
                    json.push('\n');
                    json.push_str(&pretty_opts.generate_indent());
                }
                json.push(']');
            }
            OBJECT_CONTAINER_TAG => {
                if pretty_opts.enabled {
                    json.push_str("{\n");
                } else {
                    json.push('{');
                }
                let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
                let mut jentry_offset = 4 + *offset;
                let mut key_offset = 4 + *offset + 8 * length;
                let mut keys = VecDeque::with_capacity(length);
                for _ in 0..length {
                    let jentry_encoded = read_u32(value, jentry_offset)?;
                    let jentry = JEntry::decode_jentry(jentry_encoded);
                    let key_length = jentry.length as usize;
                    keys.push_back((key_offset, key_offset + key_length));
                    jentry_offset += 4;
                    key_offset += key_length;
                }
                let mut value_offset = key_offset;
                let inner_pretty_ops = pretty_opts.inc_indent();
                for i in 0..length {
                    if i > 0 {
                        if pretty_opts.enabled {
                            json.push_str(",\n");
                        } else {
                            json.push(',');
                        }
                    }
                    let (key_start, key_end) = keys.pop_front().unwrap();
                    if pretty_opts.enabled {
                        json.push_str(&inner_pretty_ops.generate_indent());
                        Self::escape_scalar_string(value, key_start, key_end, json);
                        json.push_str(": ");
                    } else {
                        Self::escape_scalar_string(value, key_start, key_end, json);
                        json.push(':');
                    }
                    Self::scalar_to_string(
                        value,
                        &mut jentry_offset,
                        &mut value_offset,
                        json,
                        &inner_pretty_ops,
                    )?;
                }
                if pretty_opts.enabled {
                    json.push('\n');
                    json.push_str(&pretty_opts.generate_indent());
                }
                json.push('}');
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }
        Ok(())
    }

    fn scalar_to_string(
        value: &[u8],
        jentry_offset: &mut usize,
        value_offset: &mut usize,
        json: &mut String,
        pretty_opts: &PrettyOpts,
    ) -> Result<(), Error> {
        let jentry_encoded = read_u32(value, *jentry_offset)?;
        let jentry = JEntry::decode_jentry(jentry_encoded);
        let length = jentry.length as usize;
        match jentry.type_code {
            NULL_TAG => json.push_str("null"),
            TRUE_TAG => json.push_str("true"),
            FALSE_TAG => json.push_str("false"),
            NUMBER_TAG => {
                let num = Number::decode(&value[*value_offset..*value_offset + length])?;
                json.push_str(&num.to_string());
            }
            STRING_TAG => {
                Self::escape_scalar_string(value, *value_offset, *value_offset + length, json);
            }
            CONTAINER_TAG => {
                Self::container_to_string(value, value_offset, json, pretty_opts)?;
            }
            _ => {}
        }
        *jentry_offset += 4;
        *value_offset += length;
        Ok(())
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
}

impl Eq for RawJsonb<'_> {}

/// `JSONB` values supports partial decode for comparison,
/// if the values are found to be unequal, the result will be returned immediately.
/// In first level header, values compare as the following order:
/// Scalar Null > Array > Object > Other Scalars(String > Number > Boolean).
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

impl Ord for RawJsonb<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ordering) => ordering,
            None => Ordering::Equal,
        }
    }
}

pub(crate) fn extract_by_jentry(
    jentry: &JEntry,
    encoded: u32,
    offset: usize,
    value: &[u8],
) -> Vec<u8> {
    let length = jentry.length as usize;
    match jentry.type_code {
        CONTAINER_TAG => value[offset..offset + length].to_vec(),
        _ => {
            let mut buf = Vec::with_capacity(8 + length);
            buf.extend_from_slice(&SCALAR_CONTAINER_TAG.to_be_bytes());
            buf.extend_from_slice(&encoded.to_be_bytes());
            if jentry.length > 0 {
                buf.extend_from_slice(&value[offset..offset + length]);
            }
            buf
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

struct PrettyOpts {
    enabled: bool,
    indent: usize,
}

impl PrettyOpts {
    fn new(enabled: bool) -> Self {
        Self { enabled, indent: 0 }
    }

    fn inc_indent(&self) -> Self {
        Self {
            enabled: self.enabled,
            indent: self.indent + 2,
        }
    }

    fn generate_indent(&self) -> String {
        String::from_utf8(vec![0x20; self.indent]).unwrap()
    }
}

pub(crate) fn read_u32(buf: &[u8], idx: usize) -> Result<u32, Error> {
    let bytes: [u8; 4] = buf
        .get(idx..idx + 4)
        .ok_or(Error::InvalidEOF)?
        .try_into()
        .unwrap();
    Ok(u32::from_be_bytes(bytes))
}
