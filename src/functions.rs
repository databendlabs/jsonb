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
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::str::from_utf8;
use std::str::from_utf8_unchecked;

use crate::builder::ArrayBuilder;
use crate::builder::ObjectBuilder;
use crate::constants::*;
use crate::error::*;
use crate::iterator::iteate_object_keys;
use crate::iterator::iterate_array;
use crate::iterator::iterate_object_entries;
use crate::jentry::JEntry;
use crate::jsonpath::JsonPath;
use crate::jsonpath::Mode;
use crate::jsonpath::Selector;
use crate::keypath::KeyPath;
use crate::number::Number;
use crate::parser::parse_value;

use crate::OwnedJsonb;
use crate::RawJsonb;

// builtin functions for `JSONB` bytes and `JSON` strings without decode all Values.
// The input value must be valid `JSONB' or `JSON`.

impl OwnedJsonb {
    /// Builds a JSONB array from a collection of RawJsonb values.
    ///
    /// This function constructs a new JSONB array from an iterator of `RawJsonb` values.  The resulting `OwnedJsonb` represents the binary encoding of the array.  The input iterator must be an `ExactSizeIterator` to allow for efficient pre-allocation of the output buffer.
    ///
    /// # Arguments
    ///
    /// * `items` - An iterator of `RawJsonb` values representing the elements of the array.  Must be an `ExactSizeIterator`.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The newly created JSONB array.
    /// * `Err(Error)` - If any of the input `RawJsonb` values are invalid or if an error occurs during array construction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Create some RawJsonb values
    /// let owned_num = "1".parse::<OwnedJsonb>().unwrap();
    /// let owned_str = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let owned_arr = "[1,2,3]".parse::<OwnedJsonb>().unwrap();
    ///
    /// // Build the array
    /// let raw_jsonbs = vec![owned_num.as_raw(), owned_str.as_raw(), owned_arr.as_raw()];
    /// let array_result = OwnedJsonb::build_array(raw_jsonbs.into_iter());
    /// assert!(array_result.is_ok());
    /// let array = array_result.unwrap();
    ///
    /// // Convert to string for easy verification
    /// assert_eq!(array.to_string(), "[1,\"hello\",[1,2,3]]");
    ///
    /// // Example with an empty iterator
    /// let empty_array = OwnedJsonb::build_array(<[RawJsonb<'_>; 0] as IntoIterator>::into_iter([])).unwrap();
    /// assert_eq!(empty_array.to_string(), "[]");
    ///
    /// // Example with invalid input (this will cause an error)
    /// let invalid_data = OwnedJsonb::new(vec![1,2,3,4]);
    /// let result = OwnedJsonb::build_array([invalid_data.as_raw()].into_iter());
    /// assert!(result.is_err());
    /// ```
    pub fn build_array<'a>(
        items: impl IntoIterator<Item = RawJsonb<'a>>,
    ) -> Result<OwnedJsonb, Error> {
        let mut jentries = Vec::new();
        let mut data = Vec::new();
        for value in items.into_iter() {
            let header = read_u32(value.data, 0)?;
            let encoded_jentry = match header & CONTAINER_HEADER_TYPE_MASK {
                SCALAR_CONTAINER_TAG => {
                    let jentry = &value.data[4..8];
                    data.extend_from_slice(&value.data[8..]);
                    jentry.try_into().unwrap()
                }
                ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG => {
                    data.extend_from_slice(value.data);
                    (CONTAINER_TAG | value.data.len() as u32).to_be_bytes()
                }
                _ => return Err(Error::InvalidJsonbHeader),
            };
            jentries.push(encoded_jentry);
        }
        let len = jentries.len();
        // reserve space for header, jentries and value data
        let mut buf = Vec::with_capacity(data.len() + len * 4 + 4);
        // write header
        let header = ARRAY_CONTAINER_TAG | (len as u32);
        buf.extend_from_slice(&header.to_be_bytes());
        // write jentries
        for jentry in jentries.into_iter() {
            buf.extend_from_slice(&jentry);
        }
        buf.extend_from_slice(&data);
        Ok(OwnedJsonb::new(buf))
    }

    /// Builds a JSONB object from a collection of key-value pairs.
    ///
    /// This function constructs a new JSONB object from an iterator of key-value pairs. The keys are strings, and the values are `RawJsonb` values. The resulting `OwnedJsonb` represents the binary encoding of the object. The input iterator must be an `ExactSizeIterator` to allow for efficient pre-allocation of the output buffer.
    ///
    /// # Arguments
    ///
    /// * `items` - An iterator of `(K, &'a RawJsonb<'a>)` tuples, where `K` is a type that can be converted into a string slice (`AsRef<str>`) representing the key, and the second element is a `RawJsonb` representing the value. Must be an `ExactSizeIterator`.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The newly created JSONB object.
    /// * `Err(Error)` - If any of the input `RawJsonb` values are invalid, if any key is not valid UTF-8, or if an error occurs during object construction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Create some RawJsonb values
    /// let owned_num = "1".parse::<OwnedJsonb>().unwrap();
    /// let owned_str = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let owned_arr = "[1,2,3]".parse::<OwnedJsonb>().unwrap();
    ///
    /// // Build the object
    /// let raw_jsonbs = vec![("a", owned_num.as_raw()), ("b", owned_str.as_raw()), ("c", owned_arr.as_raw())];
    /// let object_result = OwnedJsonb::build_object(raw_jsonbs.into_iter());
    /// assert!(object_result.is_ok());
    /// let object = object_result.unwrap();
    ///
    /// // Convert to string for easy verification
    /// assert_eq!(object.to_string(), r#"{"a":1,"b":"hello","c":[1,2,3]}"#);
    ///
    /// // Example with an empty iterator
    /// let empty_object = OwnedJsonb::build_object(<[(&str, RawJsonb<'_>); 0] as IntoIterator>::into_iter([])).unwrap();
    /// assert_eq!(empty_object.to_string(), "{}");
    ///
    /// // Example with invalid value
    /// let invalid_data = OwnedJsonb::new(vec![1,2,3,4]);
    /// let result = OwnedJsonb::build_object([("a", invalid_data.as_raw())].into_iter());
    /// assert!(result.is_err());
    /// ```
    pub fn build_object<'a, K: AsRef<str>>(
        items: impl IntoIterator<Item = (K, RawJsonb<'a>)>,
    ) -> Result<OwnedJsonb, Error> {
        let mut key_jentries = Vec::new();
        let mut val_jentries = Vec::new();
        let mut key_data = Vec::new();
        let mut val_data = Vec::new();

        for (key, value) in items.into_iter() {
            let key = key.as_ref();
            // write key jentry and key data
            let encoded_key_jentry = (STRING_TAG | key.len() as u32).to_be_bytes();
            key_jentries.push(encoded_key_jentry);
            key_data.extend_from_slice(key.as_bytes());

            // build value jentry and write value data
            let header = read_u32(value.data, 0)?;
            let encoded_val_jentry = match header & CONTAINER_HEADER_TYPE_MASK {
                SCALAR_CONTAINER_TAG => {
                    let jentry = &value.data[4..8];
                    val_data.extend_from_slice(&value.data[8..]);
                    jentry.try_into().unwrap()
                }
                ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG => {
                    val_data.extend_from_slice(value.data);
                    (CONTAINER_TAG | value.data.len() as u32).to_be_bytes()
                }
                _ => return Err(Error::InvalidJsonbHeader),
            };
            val_jentries.push(encoded_val_jentry);
        }
        let len = key_jentries.len();
        // reserve space for header, jentries and value data
        let mut buf = Vec::with_capacity(key_data.len() + val_data.len() + len * 8 + 4);
        // write header
        let header = OBJECT_CONTAINER_TAG | (len as u32);
        buf.extend_from_slice(&header.to_be_bytes());
        // write key jentries
        for jentry in key_jentries.into_iter() {
            buf.extend_from_slice(&jentry);
        }
        // write value jentries
        for jentry in val_jentries.into_iter() {
            buf.extend_from_slice(&jentry);
        }
        // write key data and value data
        buf.extend_from_slice(&key_data);
        buf.extend_from_slice(&val_data);
        Ok(OwnedJsonb::new(buf))
    }
}

impl RawJsonb<'_> {
    /// Returns the number of elements in a JSONB array.
    ///
    /// This function checks the header of the JSONB data to determine if it represents an array.
    /// If it is an array, the function returns the number of elements in the array.  If the JSONB
    /// data is not an array (e.g., it's an object or a scalar value), the function returns `None`.
    /// An error is returned if the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let arr_jsonb = "[1,2,3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let len = raw_jsonb.array_length().unwrap();
    /// assert_eq!(len, Some(3));
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": {"c": 2, "d": 3}}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let len = raw_jsonb.array_length().unwrap();
    /// assert_eq!(len, None);
    /// ```
    pub fn array_length(&self) -> Result<Option<usize>, Error> {
        let header = read_u32(self.data, 0)?;
        let len = match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
                Some(length)
            }
            OBJECT_CONTAINER_TAG | SCALAR_CONTAINER_TAG => None,
            _ => {
                return Err(Error::InvalidJsonb);
            }
        };
        Ok(len)
    }

    /// Checks if the JSONB value contains other JSONB value.
    ///
    /// Containment is defined as follows:
    ///
    /// * **Scalar values:** Two scalar values are considered equal if their byte representations are identical.
    /// * **Objects:** The self object contains the other object if all key-value pairs in the other object
    ///   exist in the self object with the same values.  The self object may have additional key-value pairs.
    /// * **Arrays:** The self array contains the other array if, for every element in the other array, there exists
    ///   an identical element in the self array.  The self array may have additional elements.  Note that order does
    ///   **not** matter for containment, and duplicate elements are handled correctly. Nested arrays are also supported.
    ///
    /// # Arguments
    ///
    /// * `self` - The self JSONB value.
    /// * `other` - The other JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` if the self JSONB value contains the other JSONB value.
    /// * `Ok(false)` if the self JSONB value does not contain the other JSONB value.
    /// * `Err(Error)` if an error occurred during decoding.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Example 1: Array containment
    /// let left_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let left_raw = left_jsonb.as_raw();
    /// let right_jsonb = "[3, 1]".parse::<OwnedJsonb>().unwrap();
    /// let right_raw = right_jsonb.as_raw();
    /// assert!(left_raw.contains(&right_raw).unwrap());
    ///
    /// // Example 2: Object containment with nested structures
    /// let left_jsonb = r#"{"a": 1, "b": {"c": 2, "d": 3}}"#.parse::<OwnedJsonb>().unwrap();
    /// let left_raw = left_jsonb.as_raw();
    /// let right_jsonb = r#"{"b": {"c": 2}}"#.parse::<OwnedJsonb>().unwrap();
    /// let right_raw = right_jsonb.as_raw();
    /// assert!(left_raw.contains(&right_raw).unwrap());
    /// ```
    pub fn contains(&self, other: &RawJsonb) -> Result<bool, Error> {
        let left = self.data;
        let right = other.data;
        Self::containter_contains(left, right)
    }

    fn containter_contains(left: &[u8], right: &[u8]) -> Result<bool, Error> {
        let l_header = read_u32(left, 0)?;
        let r_header = read_u32(right, 0)?;

        let l_type = l_header & CONTAINER_HEADER_TYPE_MASK;
        let r_type = r_header & CONTAINER_HEADER_TYPE_MASK;

        // special case for the left array and the right scalar
        if l_type == ARRAY_CONTAINER_TAG && r_type == SCALAR_CONTAINER_TAG {
            let r_jentry = JEntry::decode_jentry(read_u32(right, 4)?);
            return Ok(Self::array_contains(left, l_header, &right[8..], r_jentry));
        }

        if l_type != r_type {
            return Ok(false);
        }

        match r_type {
            OBJECT_CONTAINER_TAG => {
                let l_size = l_header & CONTAINER_HEADER_LEN_MASK;
                let r_size = r_header & CONTAINER_HEADER_LEN_MASK;
                if l_size < r_size {
                    return Ok(false);
                }
                for (r_key, r_jentry, r_val) in iterate_object_entries(right, r_header) {
                    match get_jentry_by_name(left, 0, l_header, r_key, false) {
                        Some((l_jentry, _, l_val_offset)) => {
                            if l_jentry.type_code != r_jentry.type_code {
                                return Ok(false);
                            }
                            let l_val =
                                &left[l_val_offset..l_val_offset + l_jentry.length as usize];
                            if r_jentry.type_code != CONTAINER_TAG {
                                if !l_val.eq(r_val) {
                                    return Ok(false);
                                }
                            } else if !Self::containter_contains(l_val, r_val)? {
                                return Ok(false);
                            }
                        }
                        None => return Ok(false),
                    }
                }
                Ok(true)
            }
            ARRAY_CONTAINER_TAG => {
                for (r_jentry, r_val) in iterate_array(right, r_header) {
                    if r_jentry.type_code != CONTAINER_TAG {
                        if !Self::array_contains(left, l_header, r_val, r_jentry) {
                            return Ok(false);
                        }
                    } else {
                        let l_nested: Vec<_> = iterate_array(left, l_header)
                            .filter(|(l_jentry, _)| l_jentry.type_code == CONTAINER_TAG)
                            .map(|(_, l_val)| l_val)
                            .collect();

                        let mut contains_nested = false;

                        for l_nested_val in l_nested {
                            if Self::containter_contains(l_nested_val, r_val)? {
                                contains_nested = true;
                                break;
                            }
                        }
                        if !contains_nested {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            _ => Ok(left.eq(right)),
        }
    }

    fn array_contains(arr: &[u8], arr_header: u32, val: &[u8], val_jentry: JEntry) -> bool {
        for (jentry, arr_val) in iterate_array(arr, arr_header) {
            if jentry.type_code != val_jentry.type_code {
                continue;
            }
            if val.eq(arr_val) {
                return true;
            }
        }
        false
    }

    /// Returns an `OwnedJsonb` array containing the keys of the JSONB object.
    ///
    /// If the JSONB value is an object, this function returns a new `OwnedJsonb` array containing the keys of the object as string values.
    /// The order of the keys in the returned array is the same as their order in the original object.
    /// If the JSONB value is not an object (e.g., it's an array or a scalar), this function returns `Ok(None)`.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(OwnedJsonb))` - An `OwnedJsonb` representing the array of keys if the input is an object.
    /// * `Ok(None)` - If the input is not an object.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Object keys
    /// let obj_jsonb = r#"{"a": 1, "b": 2, "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let keys_result = raw_jsonb.object_keys();
    /// assert!(keys_result.is_ok());
    ///
    /// let keys_jsonb = keys_result.unwrap();
    /// assert_eq!(keys_jsonb.as_ref().map(|k| k.to_string()), Some(r#"["a","b","c"]"#.to_string()));
    ///
    /// // Array - returns None
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let keys_result = raw_jsonb.object_keys();
    /// assert!(keys_result.is_ok());
    /// assert!(keys_result.unwrap().is_none());
    ///
    /// // Scalar - returns None
    /// let scalar_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = scalar_jsonb.as_raw();
    /// let keys_result = raw_jsonb.object_keys();
    /// assert!(keys_result.is_ok());
    /// assert!(keys_result.unwrap().is_none());
    /// ```
    pub fn object_keys(&self) -> Result<Option<OwnedJsonb>, Error> {
        let header = read_u32(self.data, 0)?;
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
                    let key_encoded = read_u32(self.data, jentry_offset)?;
                    let key_jentry = JEntry::decode_jentry(key_encoded);
                    buf.extend_from_slice(&key_encoded.to_be_bytes());

                    jentry_offset += 4;
                    key_offset += key_jentry.length as usize;
                    key_offsets.push(key_offset);
                }
                let mut prev_key_offset = 8 * length + 4;
                for key_offset in key_offsets {
                    if key_offset > prev_key_offset {
                        buf.extend_from_slice(&self.data[prev_key_offset..key_offset]);
                    }
                    prev_key_offset = key_offset;
                }
                Ok(Some(OwnedJsonb::new(buf)))
            }
            ARRAY_CONTAINER_TAG | SCALAR_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Iterates over the key-value pairs of a JSONB object.
    ///
    /// If the JSONB value is an object, this function returns a vector of tuples, where each tuple contains
    /// the key (as a `String`) and the value (as an `OwnedJsonb`) of a key-value pair.
    /// The order of the key-value pairs in the returned vector is the same as their order in the original object.
    /// If the JSONB value is not an object (e.g., it's an array or a scalar), this function returns `Ok(None)`.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(Vec<(String, OwnedJsonb)>))` - A vector of tuples representing the key-value pairs if the input is an object.
    /// * `Ok(None)` - If the input is not an object.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data, invalid UTF-8 key).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Object iteration
    /// let obj_jsonb = r#"{"a": 1, "b": "hello", "c": [1, 2]}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let items_result = raw_jsonb.object_each();
    /// assert!(items_result.is_ok());
    ///
    /// let items = items_result.unwrap().unwrap();
    /// assert_eq!(items.len(), 3);
    ///
    /// assert_eq!(items[0].0, "a");
    /// assert_eq!(items[0].1.to_string(), "1");
    /// assert_eq!(items[1].0, "b");
    /// assert_eq!(items[1].1.to_string(), r#""hello""#);
    /// assert_eq!(items[2].0, "c");
    /// assert_eq!(items[2].1.to_string(), r#"[1,2]"#);
    ///
    /// // Array - returns None
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let items_result = raw_jsonb.object_each();
    /// assert!(items_result.is_ok());
    /// assert!(items_result.unwrap().is_none());
    ///
    /// // Scalar - returns None
    /// let scalar_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = scalar_jsonb.as_raw();
    /// let items_result = raw_jsonb.object_each();
    /// assert!(items_result.is_ok());
    /// assert!(items_result.unwrap().is_none());
    /// ```
    pub fn object_each(&self) -> Result<Option<Vec<(String, OwnedJsonb)>>, Error> {
        let header = read_u32(self.data, 0)?;

        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {
                let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
                let mut items: Vec<(String, OwnedJsonb)> = Vec::with_capacity(length);
                let mut jentries: VecDeque<(JEntry, u32)> = VecDeque::with_capacity(length * 2);
                let mut offset = 4;

                for _ in 0..length * 2 {
                    let encoded = read_u32(self.data, offset)?;
                    offset += 4;
                    jentries.push_back((JEntry::decode_jentry(encoded), encoded));
                }

                let mut keys: VecDeque<String> = VecDeque::with_capacity(length);
                for _ in 0..length {
                    let (jentry, _) = jentries.pop_front().unwrap();
                    let key_len = jentry.length as usize;
                    let key_data = self.data[offset..offset + key_len].to_vec();
                    let key = String::from_utf8(key_data).map_err(|_| Error::InvalidJsonb)?;
                    keys.push_back(key);
                    offset += key_len;
                }

                for _ in 0..length {
                    let (jentry, encoded) = jentries.pop_front().unwrap();
                    let key = keys.pop_front().unwrap();
                    let val_length = jentry.length as usize;
                    let val_data = extract_by_jentry(&jentry, encoded, offset, self.data);
                    let val = OwnedJsonb::new(val_data);
                    offset += val_length;
                    items.push((key, val));
                }
                Ok(Some(items))
            }
            ARRAY_CONTAINER_TAG | SCALAR_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Extracts the values from a JSONB array.
    ///
    /// If the JSONB value is an array, this function returns a vector of `OwnedJsonb` representing the array elements.
    /// If the JSONB value is not an array (e.g., it's an object or a scalar), this function returns `Ok(None)`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(Vec<OwnedJsonb>))` - A vector of `OwnedJsonb` values if the input is an array.
    /// * `Ok(None)` - If the input is not an array.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Array values extraction
    /// let arr_jsonb = r#"[1, "hello", {"a": 1}]"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let values_result = raw_jsonb.array_values();
    /// assert!(values_result.is_ok());
    ///
    /// let values = values_result.unwrap().unwrap();
    /// assert_eq!(values.len(), 3);
    ///
    /// assert_eq!(values[0].to_string(), "1");
    /// assert_eq!(values[1].to_string(), r#""hello""#);
    /// assert_eq!(values[2].to_string(), r#"{"a":1}"#);
    ///
    /// // Object - returns None
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let values_result = raw_jsonb.array_values();
    /// assert!(values_result.is_ok());
    /// assert!(values_result.unwrap().is_none());
    ///
    /// // Scalar - returns None
    /// let scalar_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = scalar_jsonb.as_raw();
    /// let values_result = raw_jsonb.array_values();
    /// assert!(values_result.is_ok());
    /// assert!(values_result.unwrap().is_none());
    /// ```
    pub fn array_values(&self) -> Result<Option<Vec<OwnedJsonb>>, Error> {
        let header = read_u32(self.data, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
                let mut jentry_offset = 4;
                let mut val_offset = 4 * length + 4;
                let mut items = Vec::with_capacity(length);
                for _ in 0..length {
                    let encoded = read_u32(self.data, jentry_offset)?;
                    let jentry = JEntry::decode_jentry(encoded);
                    let val_length = jentry.length as usize;
                    let item_data = extract_by_jentry(&jentry, encoded, val_offset, self.data);
                    let item = OwnedJsonb::new(item_data);
                    items.push(item);

                    jentry_offset += 4;
                    val_offset += val_length;
                }
                Ok(Some(items))
            }
            OBJECT_CONTAINER_TAG | SCALAR_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Determines the type of a JSONB value.
    ///
    /// This function returns a string representation of the JSONB value's type.
    /// The possible return values are:
    /// * `"null"`
    /// * `"boolean"`
    /// * `"number"`
    /// * `"string"`
    /// * `"array"`
    /// * `"object"`
    ///
    /// # Returns
    ///
    /// * `Ok(&'static str)` - A string slice representing the type of the JSONB value.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Type checking
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "array");
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "object");
    ///
    /// let num_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = num_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "number");
    ///
    /// let string_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = string_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "string");
    ///
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = bool_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "boolean");
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = null_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "null");
    /// ```
    pub fn type_of(&self) -> Result<&'static str, Error> {
        let value = self.data;
        let header = read_u32(value, 0)?;

        match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(value, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                match jentry.type_code {
                    NULL_TAG => Ok(TYPE_NULL),
                    TRUE_TAG | FALSE_TAG => Ok(TYPE_BOOLEAN),
                    NUMBER_TAG => Ok(TYPE_NUMBER),
                    STRING_TAG => Ok(TYPE_STRING),
                    _ => Err(Error::InvalidJsonbJEntry),
                }
            }
            ARRAY_CONTAINER_TAG => Ok(TYPE_ARRAY),
            OBJECT_CONTAINER_TAG => Ok(TYPE_OBJECT),
            _ => Err(Error::InvalidJsonbHeader),
        }
    }

    /// Checks if the JSONB value is null.
    ///
    /// This function determines whether the JSONB value represents a JSON `null`.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` if the value is null.
    /// * `Ok(false)` if the value is not null.
    /// * `Err(Error)` if an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = null_jsonb.as_raw();
    /// assert!(raw_jsonb.is_null().unwrap());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// assert!(!raw_jsonb.is_null().unwrap());
    /// ```
    pub fn is_null(&self) -> Result<bool, Error> {
        self.as_null().map(|v| v.is_some())
    }

    /// Checks if the JSONB value is null.
    ///
    /// This function checks if the JSONB value represents a JSON `null` value.
    /// It returns `Some(())` if the value is null and `None` otherwise.
    /// Note that this function only checks for the specific JSON `null` type; it doesn't check for empty objects or arrays.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(()))` - If the value is JSON `null`.
    /// * `Ok(None)` - If the value is not JSON `null`.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // JSON null
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = null_jsonb.as_raw();
    /// assert!(raw_jsonb.as_null().unwrap().is_some());
    ///
    /// // Non-null values
    /// let num_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = num_jsonb.as_raw();
    /// assert!(raw_jsonb.as_null().unwrap().is_none());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// assert!(raw_jsonb.as_null().unwrap().is_none());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// assert!(raw_jsonb.as_null().unwrap().is_none());
    ///
    /// let empty_array_jsonb = "[]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = empty_array_jsonb.as_raw();
    /// assert!(raw_jsonb.as_null().unwrap().is_none());
    ///
    /// let empty_object_jsonb = "{}".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = empty_object_jsonb.as_raw();
    /// assert!(raw_jsonb.as_null().unwrap().is_none());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.as_null();
    /// assert!(result.is_err());
    /// ```
    pub fn as_null(&self) -> Result<Option<()>, Error> {
        let header = read_u32(self.data, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let jentry_encoded = read_u32(self.data, 4)?;
                let jentry = JEntry::decode_jentry(jentry_encoded);
                match jentry.type_code {
                    NULL_TAG => Ok(Some(())),
                    STRING_TAG | NUMBER_TAG | FALSE_TAG | TRUE_TAG | CONTAINER_TAG => Ok(None),
                    _ => Err(Error::InvalidJsonb),
                }
            }
            OBJECT_CONTAINER_TAG | ARRAY_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Checks if the JSONB value is a boolean.
    ///
    /// This function checks if the JSONB value represents a JSON boolean (`true` or `false`).
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is a boolean (`true` or `false`).
    /// * `Ok(false)` - If the value is not a boolean.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Boolean values
    /// let true_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_true = true_jsonb.as_raw();
    /// assert!(raw_true.is_boolean().unwrap());
    ///
    /// let false_jsonb = "false".parse::<OwnedJsonb>().unwrap();
    /// let raw_false = false_jsonb.as_raw();
    /// assert!(raw_false.is_boolean().unwrap());
    ///
    /// // Non-boolean values
    /// let num_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert!(!raw_num.is_boolean().unwrap());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert!(!raw_arr.is_boolean().unwrap());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert!(!raw_obj.is_boolean().unwrap());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert!(!raw_null.is_boolean().unwrap());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.is_boolean();
    /// assert!(result.is_err());
    /// ```
    pub fn is_boolean(&self) -> Result<bool, Error> {
        self.as_bool().map(|v| v.is_some())
    }

    /// Extracts a boolean value from a JSONB value.
    ///
    /// This function attempts to extract a boolean value (`true` or `false`) from the JSONB value.  If the JSONB value is a boolean, the corresponding boolean value is returned.  If the JSONB value is not a boolean (e.g., a number, string, null, array, or object), `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(true))` - If the value is JSON `true`.
    /// * `Ok(Some(false))` - If the value is JSON `false`.
    /// * `Ok(None)` - If the value is not a boolean (number, string, null, array, object).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Boolean values
    /// let true_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_true = true_jsonb.as_raw();
    /// assert_eq!(raw_true.as_bool().unwrap(), Some(true));
    ///
    /// let false_jsonb = "false".parse::<OwnedJsonb>().unwrap();
    /// let raw_false = false_jsonb.as_raw();
    /// assert_eq!(raw_false.as_bool().unwrap(), Some(false));
    ///
    /// // Non-boolean values
    /// let num_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert_eq!(raw_num.as_bool().unwrap(), None);
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert_eq!(raw_arr.as_bool().unwrap(), None);
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert_eq!(raw_obj.as_bool().unwrap(), None);
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert_eq!(raw_null.as_bool().unwrap(), None);
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.as_bool();
    /// assert!(result.is_err());
    /// ```
    pub fn as_bool(&self) -> Result<Option<bool>, Error> {
        let header = read_u32(self.data, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let jentry_encoded = read_u32(self.data, 4)?;
                let jentry = JEntry::decode_jentry(jentry_encoded);
                match jentry.type_code {
                    FALSE_TAG => Ok(Some(false)),
                    TRUE_TAG => Ok(Some(true)),
                    NULL_TAG | STRING_TAG | NUMBER_TAG | CONTAINER_TAG => Ok(None),
                    _ => Err(Error::InvalidJsonb),
                }
            }
            OBJECT_CONTAINER_TAG | ARRAY_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Converts a JSONB value to a boolean.
    ///
    /// This function attempts to convert a JSONB value to a boolean. It prioritizes extracting a boolean value directly if possible. If the value is a string, it converts the string to lowercase and checks if it's "true" or "false".  Otherwise, it returns an error.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is JSON `true` or a string that is "true" (case-insensitive).
    /// * `Ok(false)` - If the value is JSON `false` or a string that is "false" (case-insensitive).
    /// * `Err(Error::InvalidCast)` - If the value cannot be converted to a boolean (e.g., it's a number, null, array, or object, or a string that's not "true" or "false").
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Boolean values
    /// let true_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// assert!(true_jsonb.as_raw().to_bool().unwrap());
    ///
    /// let false_jsonb = "false".parse::<OwnedJsonb>().unwrap();
    /// assert!(!false_jsonb.as_raw().to_bool().unwrap());
    ///
    /// // String representations of booleans
    /// let true_str = r#""true""#.parse::<OwnedJsonb>().unwrap();
    /// assert!(true_str.as_raw().to_bool().unwrap());
    ///
    /// let false_str = r#""false""#.parse::<OwnedJsonb>().unwrap();
    /// assert!(!false_str.as_raw().to_bool().unwrap());
    ///
    /// let true_str_lowercase = r#""TRUE""#.parse::<OwnedJsonb>().unwrap();
    /// assert!(true_str_lowercase.as_raw().to_bool().unwrap());
    ///
    /// // Invalid conversions
    /// let num_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let result = num_jsonb.as_raw().to_bool();
    /// assert!(result.is_err());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let result = arr_jsonb.as_raw().to_bool();
    /// assert!(result.is_err());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let result = obj_jsonb.as_raw().to_bool();
    /// assert!(result.is_err());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let result = null_jsonb.as_raw().to_bool();
    /// assert!(result.is_err());
    ///
    /// let invalid_str = r#""maybe""#.parse::<OwnedJsonb>().unwrap();
    /// let result = invalid_str.as_raw().to_bool();
    /// assert!(result.is_err());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.to_bool();
    /// assert!(result.is_err());
    /// ```
    pub fn to_bool(&self) -> Result<bool, Error> {
        if let Some(v) = self.as_bool()? {
            return Ok(v);
        } else if let Some(v) = self.as_str()? {
            if &v.to_lowercase() == "true" {
                return Ok(true);
            } else if &v.to_lowercase() == "false" {
                return Ok(false);
            }
        }
        Err(Error::InvalidCast)
    }

    /// Checks if the JSONB value is a number.
    ///
    /// This function checks if the JSONB value represents a JSON number.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is a number.
    /// * `Ok(false)` - If the value is not a number.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Number values
    /// let num_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert!(raw_num.is_number().unwrap());
    ///
    /// let num_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert!(raw_num.is_number().unwrap());
    ///
    /// let num_jsonb = "-123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert!(raw_num.is_number().unwrap());
    ///
    /// // Non-number values
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert!(!raw_bool.is_number().unwrap());
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert!(!raw_str.is_number().unwrap());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert!(!raw_arr.is_number().unwrap());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert!(!raw_obj.is_number().unwrap());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert!(!raw_null.is_number().unwrap());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.is_number();
    /// assert!(result.is_err());
    /// ```
    pub fn is_number(&self) -> Result<bool, Error> {
        self.as_number().map(|v| v.is_some())
    }

    /// Extracts a number from a JSONB value.
    ///
    /// This function attempts to extract a number from the JSONB value. If the JSONB value is a number, it returns the number; otherwise, it returns `None`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(Number))` - If the value is a number, the extracted number.
    /// * `Ok(None)` - If the value is not a number (boolean, string, null, array, object).
    /// * `Err(Error)` - If the JSONB data is invalid or if the number cannot be decoded.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{Number, OwnedJsonb, RawJsonb};
    ///
    /// // Number value
    /// let num_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert_eq!(raw_num.as_number().unwrap(), Some(Number::Float64(123.45)));
    ///
    /// let num_jsonb = "-123".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert_eq!(raw_num.as_number().unwrap(), Some(Number::Int64(-123)));
    ///
    /// // Non-number values
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert_eq!(raw_bool.as_number().unwrap(), None);
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert_eq!(raw_str.as_number().unwrap(), None);
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert_eq!(raw_arr.as_number().unwrap(), None);
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert_eq!(raw_obj.as_number().unwrap(), None);
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert_eq!(raw_null.as_number().unwrap(), None);
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.as_number();
    /// assert!(result.is_err());
    ///
    /// // Invalid Number (corrupted data)
    /// let corrupted_num_jsonb = OwnedJsonb::new(vec![10, 0, 0, 0, 16, 0, 0, 0, 0, 1]);
    /// let corrupted_raw_num_jsonb = corrupted_num_jsonb.as_raw();
    /// let result = corrupted_raw_num_jsonb.as_number();
    /// assert!(result.is_err()); //Decodes should return Err
    /// ```
    pub fn as_number(&self) -> Result<Option<Number>, Error> {
        let header = read_u32(self.data, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let jentry_encoded = read_u32(self.data, 4)?;
                let jentry = JEntry::decode_jentry(jentry_encoded);
                match jentry.type_code {
                    NUMBER_TAG => {
                        let length = jentry.length as usize;
                        let num = Number::decode(&self.data[8..8 + length])?;
                        Ok(Some(num))
                    }
                    NULL_TAG | STRING_TAG | FALSE_TAG | TRUE_TAG | CONTAINER_TAG => Ok(None),
                    _ => Err(Error::InvalidJsonb),
                }
            }
            OBJECT_CONTAINER_TAG | ARRAY_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Checks if the JSONB value is an integer that can be represented as an i64.
    ///
    /// This function checks if the JSONB value is a number and can be converted to an `i64` without loss of information.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is an integer representable as an `i64`.
    /// * `Ok(false)` - If the value is not an integer or cannot be represented as an `i64`.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // i64 values
    /// let i64_jsonb = "123456789012345678".parse::<OwnedJsonb>().unwrap();
    /// let raw_i64 = i64_jsonb.as_raw();
    /// assert!(raw_i64.is_i64().unwrap());
    ///
    /// let i64_jsonb = "-123456789012345678".parse::<OwnedJsonb>().unwrap();
    /// let raw_i64 = i64_jsonb.as_raw();
    /// assert!(raw_i64.is_i64().unwrap());
    ///
    /// // Non-i64 values
    /// let float_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_float = float_jsonb.as_raw();
    /// assert!(!raw_float.is_i64().unwrap());
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert!(!raw_str.is_i64().unwrap());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.is_i64();
    /// assert!(result.is_err());
    /// ```
    pub fn is_i64(&self) -> Result<bool, Error> {
        self.as_i64().map(|v| v.is_some())
    }

    /// Extracts an i64 integer from a JSONB value.
    ///
    /// This function attempts to extract an `i64` integer from the JSONB value. If the JSONB value is a number and can be represented as an `i64` without loss of information, the integer value is returned. Otherwise, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(i64))` - If the value is an integer that can be represented as an `i64`.
    /// * `Ok(None)` - If the value is not an integer or cannot be represented as an `i64` (e.g., it's a floating-point number, a boolean, string, null, array, or object).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // i64 value
    /// let i64_jsonb = "123456789012345678".parse::<OwnedJsonb>().unwrap();
    /// let raw_i64 = i64_jsonb.as_raw();
    /// assert_eq!(raw_i64.as_i64().unwrap(), Some(123456789012345678));
    ///
    /// // Non-i64 values
    /// let float_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_float = float_jsonb.as_raw();
    /// assert_eq!(raw_float.as_i64().unwrap(), None);
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert_eq!(raw_str.as_i64().unwrap(), None);
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert_eq!(raw_arr.as_i64().unwrap(), None);
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert_eq!(raw_obj.as_i64().unwrap(), None);
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.as_i64();
    /// assert!(result.is_err());
    /// ```
    pub fn as_i64(&self) -> Result<Option<i64>, Error> {
        match self.as_number()? {
            Some(num) => Ok(num.as_i64()),
            None => Ok(None),
        }
    }

    /// Converts a JSONB value to an i64 integer.
    ///
    /// This function attempts to convert a JSONB value to an `i64` integer. It prioritizes direct conversion from a number if possible.  If the value is a boolean, it's converted to 1 (for `true`) or 0 (for `false`). If the value is a string that can be parsed as an `i64`, that parsed value is returned. Otherwise, an error is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(i64)` - The `i64` representation of the JSONB value.
    /// * `Err(Error::InvalidCast)` - If the value cannot be converted to an `i64` (e.g., it's a floating-point number, an array, an object, or a string that is not a valid integer).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Integer values
    /// let i64_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(i64_jsonb.as_raw().to_i64().unwrap(), 123);
    ///
    /// let i64_jsonb = "-42".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(i64_jsonb.as_raw().to_i64().unwrap(), -42);
    ///
    /// // Boolean values
    /// let true_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(true_jsonb.as_raw().to_i64().unwrap(), 1);
    ///
    /// let false_jsonb = "false".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(false_jsonb.as_raw().to_i64().unwrap(), 0);
    ///
    /// // String representation of an integer
    /// let str_jsonb = r#""123""#.parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(str_jsonb.as_raw().to_i64().unwrap(), 123);
    ///
    /// // Invalid conversions
    /// let float_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let result = float_jsonb.as_raw().to_i64();
    /// assert!(result.is_err());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let result = arr_jsonb.as_raw().to_i64();
    /// assert!(result.is_err());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let result = obj_jsonb.as_raw().to_i64();
    /// assert!(result.is_err());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let result = null_jsonb.as_raw().to_i64();
    /// assert!(result.is_err());
    ///
    /// let invalid_str_jsonb = r#""abc""#.parse::<OwnedJsonb>().unwrap();
    /// let result = invalid_str_jsonb.as_raw().to_i64();
    /// assert!(result.is_err());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.to_i64();
    /// assert!(result.is_err());
    /// ```
    pub fn to_i64(&self) -> Result<i64, Error> {
        if let Some(v) = self.as_i64()? {
            return Ok(v);
        } else if let Some(v) = self.as_bool()? {
            if v {
                return Ok(1_i64);
            } else {
                return Ok(0_i64);
            }
        } else if let Some(v) = self.as_str()? {
            if let Ok(v) = v.parse::<i64>() {
                return Ok(v);
            }
        }
        Err(Error::InvalidCast)
    }

    /// Checks if the JSONB value is an unsigned integer that can be represented as a u64.
    ///
    /// This function checks if the JSONB value is a number and can be converted to a `u64` without loss of information.  Negative numbers will always return `false`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is an unsigned integer representable as a `u64`.
    /// * `Ok(false)` - If the value is not an unsigned integer or cannot be represented as a `u64`.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // u64 values
    /// let u64_jsonb = "1234567890123456789".parse::<OwnedJsonb>().unwrap();
    /// let raw_u64 = u64_jsonb.as_raw();
    /// assert!(raw_u64.is_u64().unwrap());
    ///
    /// let u64_jsonb = "0".parse::<OwnedJsonb>().unwrap();
    /// let raw_u64 = u64_jsonb.as_raw();
    /// assert!(raw_u64.is_u64().unwrap());
    ///
    /// // Non-u64 values
    /// let float_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_float = float_jsonb.as_raw();
    /// assert!(!raw_float.is_u64().unwrap());
    ///
    /// let negative_num_jsonb = "-123".parse::<OwnedJsonb>().unwrap();
    /// let raw_neg = negative_num_jsonb.as_raw();
    /// assert!(!raw_neg.is_u64().unwrap()); // Negative numbers are not u64
    ///
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert!(!raw_bool.is_u64().unwrap());
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert!(!raw_str.is_u64().unwrap());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert!(!raw_arr.is_u64().unwrap());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert!(!raw_obj.is_u64().unwrap());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert!(!raw_null.is_u64().unwrap());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.is_u64();
    /// assert!(result.is_err());
    /// ```
    pub fn is_u64(&self) -> Result<bool, Error> {
        self.as_u64().map(|v| v.is_some())
    }

    /// Extracts a u64 unsigned integer from a JSONB value.
    ///
    /// This function attempts to extract a `u64` unsigned integer from the JSONB value. If the JSONB value is a number and can be represented as a `u64` without loss of information (i.e., it's a non-negative integer within the `u64` range), the unsigned integer value is returned. Otherwise, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(u64))` - If the value is an unsigned integer that can be represented as a `u64`.
    /// * `Ok(None)` - If the value is not an unsigned integer or cannot be represented as a `u64` (e.g., it's a floating-point number, a negative number, a boolean, string, null, array, or object).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // u64 value
    /// let u64_jsonb = "1234567890123456789".parse::<OwnedJsonb>().unwrap();
    /// let raw_u64 = u64_jsonb.as_raw();
    /// assert_eq!(raw_u64.as_u64().unwrap(), Some(1234567890123456789));
    ///
    /// // Non-u64 values
    /// let float_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_float = float_jsonb.as_raw();
    /// assert_eq!(raw_float.as_u64().unwrap(), None);
    ///
    /// let negative_num_jsonb = "-123".parse::<OwnedJsonb>().unwrap();
    /// let raw_neg = negative_num_jsonb.as_raw();
    /// assert_eq!(raw_neg.as_u64().unwrap(), None); // Negative numbers are not u64
    ///
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert_eq!(raw_bool.as_u64().unwrap(), None);
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert_eq!(raw_str.as_u64().unwrap(), None);
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert_eq!(raw_arr.as_u64().unwrap(), None);
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert_eq!(raw_obj.as_u64().unwrap(), None);
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert_eq!(raw_null.as_u64().unwrap(), None);
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.as_u64();
    /// assert!(result.is_err());
    /// ```
    pub fn as_u64(&self) -> Result<Option<u64>, Error> {
        match self.as_number()? {
            Some(num) => Ok(num.as_u64()),
            None => Ok(None),
        }
    }

    /// Converts a JSONB value to a u64 unsigned integer.
    ///
    /// This function attempts to convert a JSONB value to a `u64` unsigned integer. It prioritizes direct conversion from a number if possible. If the value is a boolean, it's converted to 1 (for `true`) or 0 (for `false`). If the value is a string that can be parsed as a `u64`, that parsed value is returned. Otherwise, an error is returned.  Note that negative numbers cannot be converted to `u64`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(u64)` - The `u64` representation of the JSONB value.
    /// * `Err(Error::InvalidCast)` - If the value cannot be converted to a `u64` (e.g., it's a floating-point number, a negative number, an array, an object, or a string that is not a valid unsigned integer).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // u64 values
    /// let u64_jsonb = "1234567890123456789".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(u64_jsonb.as_raw().to_u64().unwrap(), 1234567890123456789);
    ///
    /// let u64_jsonb = "0".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(u64_jsonb.as_raw().to_u64().unwrap(), 0);
    ///
    /// // Boolean values
    /// let true_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(true_jsonb.as_raw().to_u64().unwrap(), 1);
    ///
    /// let false_jsonb = "false".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(false_jsonb.as_raw().to_u64().unwrap(), 0);
    ///
    /// // String representation of an unsigned integer
    /// let str_jsonb = r#""123""#.parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(str_jsonb.as_raw().to_u64().unwrap(), 123);
    ///
    /// // Invalid conversions
    /// let float_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let result = float_jsonb.as_raw().to_u64();
    /// assert!(result.is_err());
    ///
    /// let negative_num_jsonb = "-123".parse::<OwnedJsonb>().unwrap();
    /// let result = negative_num_jsonb.as_raw().to_u64();
    /// assert!(result.is_err()); // Negative numbers are not u64
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let result = arr_jsonb.as_raw().to_u64();
    /// assert!(result.is_err());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let result = obj_jsonb.as_raw().to_u64();
    /// assert!(result.is_err());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let result = null_jsonb.as_raw().to_u64();
    /// assert!(result.is_err());
    ///
    /// let invalid_str_jsonb = r#""abc""#.parse::<OwnedJsonb>().unwrap();
    /// let result = invalid_str_jsonb.as_raw().to_u64();
    /// assert!(result.is_err());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.to_u64();
    /// assert!(result.is_err());
    /// ```
    pub fn to_u64(&self) -> Result<u64, Error> {
        if let Some(v) = self.as_u64()? {
            return Ok(v);
        } else if let Some(v) = self.as_bool()? {
            if v {
                return Ok(1_u64);
            } else {
                return Ok(0_u64);
            }
        } else if let Some(v) = self.as_str()? {
            if let Ok(v) = v.parse::<u64>() {
                return Ok(v);
            }
        }
        Err(Error::InvalidCast)
    }

    /// Checks if the JSONB value is a floating-point number that can be represented as an f64.
    ///
    /// This function checks if the JSONB value is a number and can be converted to an `f64` without loss of information (this is generally always true for numbers in JSONB).
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is a number.
    /// * `Ok(false)` - If the value is not a number (boolean, string, null, array, object).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // f64 values
    /// let f64_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_f64 = f64_jsonb.as_raw();
    /// assert!(raw_f64.is_f64().unwrap());
    ///
    /// let f64_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_f64 = f64_jsonb.as_raw();
    /// assert!(raw_f64.is_f64().unwrap());
    ///
    /// let f64_jsonb = "-123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_f64 = f64_jsonb.as_raw();
    /// assert!(raw_f64.is_f64().unwrap());
    ///
    /// // Non-f64 values
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert!(!raw_bool.is_f64().unwrap());
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert!(!raw_str.is_f64().unwrap());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert!(!raw_arr.is_f64().unwrap());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert!(!raw_obj.is_f64().unwrap());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert!(!raw_null.is_f64().unwrap());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.is_f64();
    /// assert!(result.is_err());
    /// ```
    pub fn is_f64(&self) -> Result<bool, Error> {
        self.as_f64().map(|v| v.is_some())
    }

    /// Extracts an f64 floating-point number from a JSONB value.
    ///
    /// This function attempts to extract an `f64` floating-point number from the JSONB value. If the JSONB value is a number, it's converted to an `f64` and returned. Otherwise, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(f64))` - If the value is a number, the extracted `f64` value.
    /// * `Ok(None)` - If the value is not a number (boolean, string, null, array, object).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // f64 values
    /// let f64_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// let raw_f64 = f64_jsonb.as_raw();
    /// assert_eq!(raw_f64.as_f64().unwrap(), Some(123.45));
    ///
    /// let int_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_int = int_jsonb.as_raw();
    /// assert_eq!(raw_int.as_f64().unwrap(), Some(123.0));
    ///
    /// // Non-f64 values
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert_eq!(raw_bool.as_f64().unwrap(), None);
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert_eq!(raw_str.as_f64().unwrap(), None);
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert_eq!(raw_arr.as_f64().unwrap(), None);
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert_eq!(raw_obj.as_f64().unwrap(), None);
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert_eq!(raw_null.as_f64().unwrap(), None);
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.as_f64();
    /// assert!(result.is_err());
    /// ```
    pub fn as_f64(&self) -> Result<Option<f64>, Error> {
        match self.as_number()? {
            Some(num) => Ok(num.as_f64()),
            None => Ok(None),
        }
    }

    /// Converts a JSONB value to an f64 floating-point number.
    ///
    /// This function attempts to convert a JSONB value to an `f64` floating-point number. It prioritizes direct conversion from a number if possible. If the value is a boolean, it's converted to 1.0 (for `true`) or 0.0 (for `false`). If the value is a string that can be parsed as an `f64`, that parsed value is returned. Otherwise, an error is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(f64)` - The `f64` representation of the JSONB value.
    /// * `Err(Error::InvalidCast)` - If the value cannot be converted to an `f64` (e.g., it's an array, an object, a string that is not a valid number, or a null value).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // f64 values
    /// let f64_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(f64_jsonb.as_raw().to_f64().unwrap(), 123.45);
    ///
    /// let int_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(int_jsonb.as_raw().to_f64().unwrap(), 123.0);
    ///
    /// // Boolean values
    /// let true_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(true_jsonb.as_raw().to_f64().unwrap(), 1.0);
    ///
    /// let false_jsonb = "false".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(false_jsonb.as_raw().to_f64().unwrap(), 0.0);
    ///
    /// // String representation of a number
    /// let str_jsonb = r#""123.45""#.parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(str_jsonb.as_raw().to_f64().unwrap(), 123.45);
    ///
    /// // Invalid conversions
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let result = arr_jsonb.as_raw().to_f64();
    /// assert!(result.is_err());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let result = obj_jsonb.as_raw().to_f64();
    /// assert!(result.is_err());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let result = null_jsonb.as_raw().to_f64();
    /// assert!(result.is_err());
    ///
    /// let invalid_str_jsonb = r#""abc""#.parse::<OwnedJsonb>().unwrap();
    /// let result = invalid_str_jsonb.as_raw().to_f64();
    /// assert!(result.is_err());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.to_f64();
    /// assert!(result.is_err());
    /// ```
    pub fn to_f64(&self) -> Result<f64, Error> {
        if let Some(v) = self.as_f64()? {
            return Ok(v);
        } else if let Some(v) = self.as_bool()? {
            if v {
                return Ok(1_f64);
            } else {
                return Ok(0_f64);
            }
        } else if let Some(v) = self.as_str()? {
            if let Ok(v) = v.parse::<f64>() {
                return Ok(v);
            }
        }
        Err(Error::InvalidCast)
    }

    /// Checks if the JSONB value is a string.
    ///
    /// This function checks if the JSONB value represents a JSON string.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is a string.
    /// * `Ok(false)` - If the value is not a string.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // String value
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert!(raw_str.is_string().unwrap());
    ///
    /// // Non-string values
    /// let num_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert!(!raw_num.is_string().unwrap());
    ///
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert!(!raw_bool.is_string().unwrap());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert!(!raw_arr.is_string().unwrap());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert!(!raw_obj.is_string().unwrap());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert!(!raw_null.is_string().unwrap());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.is_string();
    /// assert!(result.is_err());
    /// ```
    pub fn is_string(&self) -> Result<bool, Error> {
        self.as_str().map(|v| v.is_some())
    }

    /// Extracts a string from a JSONB value.
    ///
    /// This function attempts to extract a string from the JSONB value. If the JSONB value is a string, it returns the string as a `Cow<'_, str>`. Otherwise, it returns `None`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(Cow<'_, str>))` - If the value is a string, the extracted string.
    /// * `Ok(None)` - If the value is not a string (number, boolean, null, array, object).
    /// * `Err(Error)` - If the JSONB data is invalid or if the string is not valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use std::borrow::Cow;
    ///
    /// // String value
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert_eq!(raw_str.as_str().unwrap(), Some(Cow::Borrowed("hello")));
    ///
    /// // Non-string values
    /// let num_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert_eq!(raw_num.as_str().unwrap(), None);
    ///
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert_eq!(raw_bool.as_str().unwrap(), None);
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert_eq!(raw_arr.as_str().unwrap(), None);
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert_eq!(raw_obj.as_str().unwrap(), None);
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert_eq!(raw_null.as_str().unwrap(), None);
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.as_str();
    /// assert!(result.is_err());
    ///
    /// // Invalid UTF-8 (this will panic in the unsafe block of the original code!)
    /// let invalid_utf8_jsonb = OwnedJsonb::new(vec![10, 0, 0, 0, 16, 0, 0, 0, 0, 150, 151]); // Invalid UTF-8 bytes
    /// let invalid_raw_utf8_jsonb = invalid_utf8_jsonb.as_raw();
    /// let result = invalid_raw_utf8_jsonb.as_str();
    /// assert!(result.is_err());
    /// ```
    pub fn as_str(&self) -> Result<Option<Cow<'_, str>>, Error> {
        let header = read_u32(self.data, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let jentry_encoded = read_u32(self.data, 4)?;
                let jentry = JEntry::decode_jentry(jentry_encoded);
                match jentry.type_code {
                    STRING_TAG => {
                        let length = jentry.length as usize;
                        let s = unsafe { std::str::from_utf8_unchecked(&self.data[8..8 + length]) };
                        Ok(Some(Cow::Borrowed(s)))
                    }
                    NULL_TAG | NUMBER_TAG | FALSE_TAG | TRUE_TAG | CONTAINER_TAG => Ok(None),
                    _ => Err(Error::InvalidJsonb),
                }
            }
            OBJECT_CONTAINER_TAG | ARRAY_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Converts a JSONB value to a String.
    ///
    /// This function attempts to convert a JSONB value to a string representation.  It prioritizes direct conversion from strings.  Booleans are converted to "true" or "false", and numbers are converted to their string representations.  Other types (arrays, objects, null) will result in an error.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(String)` - The string representation of the JSONB value.
    /// * `Err(Error::InvalidCast)` - If the JSONB value cannot be converted to a string (e.g., it's an array, an object, or a null value).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // String value
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(str_jsonb.as_raw().to_str().unwrap(), "hello");
    ///
    /// // Number value
    /// let num_jsonb = "123.45".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(num_jsonb.as_raw().to_str().unwrap(), "123.45");
    ///
    /// // Boolean values
    /// let true_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(true_jsonb.as_raw().to_str().unwrap(), "true");
    ///
    /// let false_jsonb = "false".parse::<OwnedJsonb>().unwrap();
    /// assert_eq!(false_jsonb.as_raw().to_str().unwrap(), "false");
    ///
    /// // Invalid conversions
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let result = arr_jsonb.as_raw().to_str();
    /// assert!(result.is_err());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let result = obj_jsonb.as_raw().to_str();
    /// assert!(result.is_err());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let result = null_jsonb.as_raw().to_str();
    /// assert!(result.is_err());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.to_str();
    /// assert!(result.is_err());
    /// ```
    pub fn to_str(&self) -> Result<String, Error> {
        if let Some(v) = self.as_str()? {
            return Ok(v.to_string());
        } else if let Some(v) = self.as_bool()? {
            if v {
                return Ok("true".to_string());
            } else {
                return Ok("false".to_string());
            }
        } else if let Some(v) = self.as_number()? {
            return Ok(format!("{}", v));
        }
        Err(Error::InvalidCast)
    }

    /// Checks if the JSONB value is an array.
    ///
    /// This function checks if the JSONB value represents a JSON array.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is an array.
    /// * `Ok(false)` - If the value is not an array (number, string, boolean, null, object).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Array value
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert!(raw_arr.is_array().unwrap());
    ///
    /// // Non-array values
    /// let num_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert!(!raw_num.is_array().unwrap());
    ///
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert!(!raw_bool.is_array().unwrap());
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert!(!raw_str.is_array().unwrap());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert!(!raw_obj.is_array().unwrap());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert!(!raw_null.is_array().unwrap());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.is_array();
    /// assert!(result.is_err());
    /// ```
    pub fn is_array(&self) -> Result<bool, Error> {
        let header = read_u32(self.data, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => Ok(true),
            SCALAR_CONTAINER_TAG | OBJECT_CONTAINER_TAG => Ok(false),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Checks if the JSONB value is an object.
    ///
    /// This function checks if the JSONB value represents a JSON object.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is an object.
    /// * `Ok(false)` - If the value is not an object (number, string, boolean, null, array).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Object value
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_obj = obj_jsonb.as_raw();
    /// assert!(raw_obj.is_object().unwrap());
    ///
    /// // Non-object values
    /// let num_jsonb = "123".parse::<OwnedJsonb>().unwrap();
    /// let raw_num = num_jsonb.as_raw();
    /// assert!(!raw_num.is_object().unwrap());
    ///
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_bool = bool_jsonb.as_raw();
    /// assert!(!raw_bool.is_object().unwrap());
    ///
    /// let str_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_str = str_jsonb.as_raw();
    /// assert!(!raw_str.is_object().unwrap());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_arr = arr_jsonb.as_raw();
    /// assert!(!raw_arr.is_object().unwrap());
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_null = null_jsonb.as_raw();
    /// assert!(!raw_null.is_object().unwrap());
    ///
    /// // Invalid JSONB
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.is_object();
    /// assert!(result.is_err());
    /// ```
    pub fn is_object(&self) -> Result<bool, Error> {
        let header = read_u32(self.data, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => Ok(true),
            SCALAR_CONTAINER_TAG | ARRAY_CONTAINER_TAG => Ok(false),
            _ => Err(Error::InvalidJsonb),
        }
    }

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

    /// Checks if a JSON path exists within the JSONB value.
    ///
    /// This function uses the `jsonpath` crate to check if a given JSON path exists within the JSONB value.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    /// * `json_path` - The JSON path to check (from the `jsonpath` crate).
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the JSON path exists.
    /// * `Ok(false)` - If the JSON path does not exist.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation.  This could also indicate issues with the `json_path` itself.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use jsonb::jsonpath::{parse_json_path, Mode};
    ///
    /// let jsonb_value = r#"{"a": {"b": [1, 2, 3]}, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    ///
    /// // Valid paths
    /// let path1 = parse_json_path("$.a.b[1]".as_bytes()).unwrap();
    /// assert!(raw_jsonb.path_exists(&path1).unwrap());
    ///
    /// let path2 = parse_json_path("$.c".as_bytes()).unwrap();
    /// assert!(raw_jsonb.path_exists(&path2).unwrap());
    ///
    /// // Invalid paths
    /// let path3 = parse_json_path("$.a.x".as_bytes()).unwrap(); // "x" does not exist
    /// assert!(!raw_jsonb.path_exists(&path3).unwrap());
    /// ```
    pub fn path_exists<'a>(&self, json_path: &'a JsonPath<'a>) -> Result<bool, Error> {
        let selector = Selector::new(json_path, Mode::Mixed);
        selector.exists(*self)
    }

    /// Checks if a JSON path matches the JSONB value using a predicate.
    ///
    /// This function uses the `jsonpath` crate to check if a given JSON path, along with an associated predicate, matches the JSONB value.
    /// The predicate determines the conditions that the selected value(s) must satisfy for the match to be considered successful.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    /// * `json_path` - The JSON path with a predicate (from the `jsonpath` crate).  The predicate is specified within the `json_path` using the standard JSONPath syntax. For example, `$.store.book[?(@.price < 10)]` selects books with a price less than 10.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the JSON path with its predicate matches at least one value in the JSONB data.
    /// * `Ok(false)` - If the JSON path with its predicate does not match any values.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation or predicate checking. This could also indicate issues with the `json_path` itself (invalid syntax, etc.).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use jsonb::jsonpath::{parse_json_path, Mode};
    ///
    /// let jsonb_value = r#"[
    ///     {"price": 12, "title": "Book A"},
    ///     {"price": 8, "title": "Book B"},
    ///     {"price": 5, "title": "Book C"}
    /// ]"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    ///
    /// // Path with predicate (select books with price < 10)
    /// let path = parse_json_path("$[*].price < 10".as_bytes()).unwrap();
    /// assert!(raw_jsonb.path_match(&path).unwrap()); // True because Book B and Book C match.
    ///
    /// // Path with predicate (select books with title "Book D")
    /// let path = parse_json_path("$[*].title == \"Book D\"".as_bytes()).unwrap();
    /// assert!(!raw_jsonb.path_match(&path).unwrap()); // False because no book has this title.
    /// ```
    pub fn path_match<'a>(&self, json_path: &'a JsonPath<'a>) -> Result<bool, Error> {
        let selector = Selector::new(json_path, Mode::First);
        selector.predicate_match(*self)
    }

    /// Extracts values from a JSONB structure using a JSONPath expression. Handles multiple matches as a Vec<OwnedJsonb>.
    ///
    /// This function uses the `jsonpath` crate to select values from the JSONB data based on the provided JSONPath expression.
    /// This function always returns a `Vec<OwnedJsonb>`, even for a single match. This allows for consistent handling of multiple matches.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    /// * `json_path` - The JSONPath expression (from the `jsonpath` crate).
    /// * `mode` - The selection mode (`Mode::First`, `Mode::All`, `Mode::Mixed`, or `Mode::Array`) from the `jsonpath` crate.
    ///
    /// # Returns
    ///
    /// * `Ok(Vec<OwnedJsonb>)` - A vector containing the selected values.  If the path does not match any values, an empty vector `Vec::new()` is returned.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation (e.g., an invalid JSONPath expression).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use jsonb::jsonpath::{parse_json_path, Mode};
    ///
    /// let jsonb_value = r#"{"a": {"b": [1, 2, 3]}, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    ///
    /// // Mode::All (return all matches as a vector)
    /// let path = parse_json_path("$.a.b[*]".as_bytes()).unwrap();
    /// let result = raw_jsonb.get_by_path(&path, Mode::All).unwrap();
    /// assert_eq!(result.len(), 3);
    /// assert_eq!(result[0].to_string(), "1");
    /// assert_eq!(result[1].to_string(), "2");
    /// assert_eq!(result[2].to_string(), "3");
    ///
    /// // Mode::First (return first value as a vector)
    /// let result = raw_jsonb.get_by_path(&path, Mode::First).unwrap();
    /// assert_eq!(result.len(), 1);
    /// assert_eq!(result[0].to_string(), "1");
    ///
    /// // Mode::Array (return a JSONB array as a vector)
    /// let result = raw_jsonb.get_by_path(&path, Mode::Array).unwrap();
    /// assert_eq!(result.len(), 1);
    /// assert_eq!(result[0].to_string(), "[1,2,3]");
    ///
    /// // Mode::Mixed (return a JSONB value as a vector)
    /// let result = raw_jsonb.get_by_path(&path, Mode::Mixed).unwrap();
    /// assert_eq!(result.len(), 1);
    /// assert_eq!(result[0].to_string(), "[1,2,3]");
    ///
    /// // Path that does not exist
    /// let path = parse_json_path("$.x".as_bytes()).unwrap();
    /// let result = raw_jsonb.get_by_path(&path, Mode::All).unwrap();
    /// assert!(result.is_empty());
    /// ```
    pub fn get_by_path<'a>(
        &self,
        json_path: &'a JsonPath<'a>,
        mode: Mode,
    ) -> Result<Vec<OwnedJsonb>, Error> {
        let selector = Selector::new(json_path, mode);
        selector.select(*self)
    }

    /// Extracts a value from a JSONB structure using a JSONPath expression. Handles single or first match.
    ///
    /// This function uses the `jsonpath` crate to select a value from the JSONB data based on the provided JSONPath expression.
    /// This function returns an `Option<OwnedJsonb>`, suitable for cases where you expect a single or first match.
    /// Note: if the mode is `Mode::All`, behavior is same as `Mode::Mixed`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    /// * `json_path` - The JSONPath expression (from the `jsonpath` crate).
    /// * `mode` - The selection mode (`Mode::First`, `Mode::Mixed`) from the `jsonpath` crate.  `Mode::All` and `Mode::Array` are not supported by this function.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(OwnedJsonb))` - If the path matches at least one value, the first matched value.
    /// * `Ok(None)` - If the path does not match any values.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation (e.g., an invalid JSONPath expression).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use jsonb::jsonpath::{parse_json_path, Mode};
    ///
    /// let jsonb_value = r#"{"a": {"b": [1, 2, 3]}, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let path = parse_json_path("$.a.b[*]".as_bytes()).unwrap();
    ///
    /// // Mode::First (return the first value)
    /// let result = raw_jsonb.get_by_path_opt(&path, Mode::First).unwrap();
    /// assert!(result.is_some());
    /// assert_eq!(result.unwrap().to_string(), "1");
    ///
    /// // Mode::Array (return a JSONB array)
    /// let result = raw_jsonb.get_by_path_opt(&path, Mode::Array).unwrap();
    /// assert!(result.is_some());
    /// assert_eq!(result.unwrap().to_string(), "[1,2,3]");
    ///
    /// // Mode::Mixed (return a JSONB value)
    /// let result = raw_jsonb.get_by_path_opt(&path, Mode::Mixed).unwrap();
    /// assert!(result.is_some());
    /// assert_eq!(result.unwrap().to_string(), "[1,2,3]");
    ///
    /// // Path that does not exist
    /// let path = parse_json_path("$.x".as_bytes()).unwrap();
    /// let result = raw_jsonb.get_by_path_opt(&path, Mode::First).unwrap();
    /// assert!(result.is_none());
    /// ```
    pub fn get_by_path_opt<'a>(
        &self,
        json_path: &'a JsonPath<'a>,
        mode: Mode,
    ) -> Result<Option<OwnedJsonb>, Error> {
        let selector = if mode == Mode::All {
            Selector::new(json_path, Mode::Mixed)
        } else {
            Selector::new(json_path, mode)
        };
        let mut owned_jsonbs = selector.select(*self)?;
        if owned_jsonbs.is_empty() {
            Ok(None)
        } else {
            Ok(Some(owned_jsonbs.remove(0)))
        }
    }

    /// Gets the element at the specified index in a JSONB array.
    ///
    /// If the JSONB value is an array, this function returns the element at the given `index` as an `OwnedJsonb`.
    /// If the `index` is out of bounds, it returns `Ok(None)`.
    /// If the JSONB value is not an array (e.g., it's an object or a scalar), this function also returns `Ok(None)`.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the desired element.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(OwnedJsonb))` - The element at the specified index as an `OwnedJsonb` if the input is an array and the index is valid.
    /// * `Ok(None)` - If the input is not an array, or if the index is out of bounds.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let arr_jsonb = r#"[1, "hello", {"a": 1}]"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    ///
    /// let element0 = raw_jsonb.get_by_index(0).unwrap();
    /// assert_eq!(element0.unwrap().to_string(), "1");
    ///
    /// let element1 = raw_jsonb.get_by_index(1).unwrap();
    /// assert_eq!(element1.unwrap().to_string(), r#""hello""#);
    ///
    /// let element2 = raw_jsonb.get_by_index(2).unwrap();
    /// assert_eq!(element2.unwrap().to_string(), r#"{"a":1}"#);
    ///
    /// let element3 = raw_jsonb.get_by_index(3).unwrap();
    /// assert!(element3.is_none()); // Index out of bounds
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let element = raw_jsonb.get_by_index(0).unwrap();
    /// assert!(element.is_none()); // Not an array
    /// ```
    pub fn get_by_index(&self, index: usize) -> Result<Option<OwnedJsonb>, Error> {
        let value = self.data;
        let header = read_u32(value, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                let val = get_jentry_by_index(value, 0, header, index)
                    .map(|(jentry, encoded, val_offset)| {
                        extract_by_jentry(&jentry, encoded, val_offset, value)
                    })
                    .map(|v| OwnedJsonb::new(v));
                Ok(val)
            }
            SCALAR_CONTAINER_TAG | OBJECT_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Gets the value associated with a given key in a JSONB object.
    ///
    /// If the JSONB value is an object, this function searches for a key matching the provided `name`
    /// and returns the associated value as an `OwnedJsonb`.
    /// The `ignore_case` parameter controls whether the key search is case-sensitive.
    /// If the key is not found, it returns `Ok(None)`.
    /// If the JSONB value is not an object (e.g., it's an array or a scalar), this function also returns `Ok(None)`.
    ///
    /// # Arguments
    ///
    /// * `name` - The key to search for.
    /// * `ignore_case` - Whether the key search should be case-insensitive.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(OwnedJsonb))` - The value associated with the key as an `OwnedJsonb`, if the input is an object and the key is found.
    /// * `Ok(None)` - If the input is not an object, or if the key is not found.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": "hello", "c": [1, 2]}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    ///
    /// let value_a = raw_jsonb.get_by_name("a", false).unwrap();
    /// assert_eq!(value_a.unwrap().to_string(), "1");
    ///
    /// let value_b = raw_jsonb.get_by_name("b", false).unwrap();
    /// assert_eq!(value_b.unwrap().to_string(), r#""hello""#);
    ///
    /// let value_c = raw_jsonb.get_by_name("c", false).unwrap();
    /// assert_eq!(value_c.unwrap().to_string(), "[1,2]");
    ///
    /// let value_d = raw_jsonb.get_by_name("d", false).unwrap();
    /// assert!(value_d.is_none()); // Key not found
    ///
    /// // Case-insensitive search
    /// let value_a_case_insensitive = raw_jsonb.get_by_name("A", true).unwrap();
    /// assert_eq!(value_a_case_insensitive.unwrap().to_string(), "1");
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let value = raw_jsonb.get_by_name("a", false).unwrap();
    /// assert!(value.is_none()); // Not an object
    /// ```
    pub fn get_by_name(&self, name: &str, ignore_case: bool) -> Result<Option<OwnedJsonb>, Error> {
        let value = self.data;
        let header = read_u32(value, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {
                let val = get_jentry_by_name(value, 0, header, name, ignore_case)
                    .map(|(jentry, encoded, val_offset)| {
                        extract_by_jentry(&jentry, encoded, val_offset, value)
                    })
                    .map(|v| OwnedJsonb::new(v));
                Ok(val)
            }
            SCALAR_CONTAINER_TAG | ARRAY_CONTAINER_TAG => Ok(None),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Gets the value at the specified key path in a JSONB value.
    ///
    /// This function traverses the JSONB value according to the provided key path
    /// and returns the value at the final path element as an `OwnedJsonb`.
    /// The key path is an iterator of `KeyPath` elements, which can be
    /// either named keys (for objects) or array indices.
    ///
    /// If any element in the key path does not exist or if the type of the current value
    /// does not match the key path element (e.g., trying to access a named key in an array),
    /// the function returns `Ok(None)`.
    /// If the key path is empty, the function returns the original `RawJsonb` value wrapped in `Some`.
    ///
    /// # Arguments
    ///
    /// * `keypaths` - An iterator of `KeyPath` elements representing the path to traverse.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(OwnedJsonb))` - The value at the specified key path as an `OwnedJsonb`, if found.
    /// * `Ok(None)` - If the key path is invalid or leads to a non-existent value.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::borrow::Cow;
    /// use jsonb::{keypath::KeyPath, OwnedJsonb, RawJsonb};
    ///
    /// let jsonb_value = r#"{"a": {"b": [1, 2, 3], "c": "hello"}, "d": [4, 5]}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    ///
    /// // Accessing nested values
    /// let path = [KeyPath::Name(Cow::Borrowed("a")), KeyPath::Name(Cow::Borrowed("b")), KeyPath::Index(1)];
    /// let value = raw_jsonb.get_by_keypath(path.iter()).unwrap();
    /// assert_eq!(value.unwrap().to_string(), "2");
    ///
    /// let path = [KeyPath::Name(Cow::Borrowed("a")), KeyPath::Name(Cow::Borrowed("c"))];
    /// let value = raw_jsonb.get_by_keypath(path.iter()).unwrap();
    /// assert_eq!(value.unwrap().to_string(), r#""hello""#);
    ///
    /// let path = [KeyPath::Name(Cow::Borrowed("d")), KeyPath::Index(0)];
    /// let value = raw_jsonb.get_by_keypath(path.iter()).unwrap();
    /// assert_eq!(value.unwrap().to_string(), "4");
    ///
    /// // Invalid key path
    /// let path = [KeyPath::Name(Cow::Borrowed("a")), KeyPath::Name(Cow::Borrowed("x"))]; // "x" doesn't exist
    /// let value = raw_jsonb.get_by_keypath(path.iter()).unwrap();
    /// assert!(value.is_none());
    ///
    /// let path = [KeyPath::Name(Cow::Borrowed("a")), KeyPath::Index(0)]; // "a" is an object, not an array
    /// let value = raw_jsonb.get_by_keypath(path.iter()).unwrap();
    /// assert!(value.is_none());
    ///
    /// // Empty key path - returns the original value
    /// let value = raw_jsonb.get_by_keypath([].iter()).unwrap();
    /// assert_eq!(value.unwrap().to_string(), r#"{"a":{"b":[1,2,3],"c":"hello"},"d":[4,5]}"#);
    ///
    /// // KeyPath with quoted name
    /// let jsonb_value = r#"{"a b": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let path = [KeyPath::QuotedName(Cow::Borrowed("a b"))];
    /// let value = raw_jsonb.get_by_keypath(path.iter()).unwrap();
    /// assert_eq!(value.unwrap().to_string(), r#"1"#);
    /// ```
    pub fn get_by_keypath<'a, I: Iterator<Item = &'a KeyPath<'a>>>(
        &self,
        keypaths: I,
    ) -> Result<Option<OwnedJsonb>, Error> {
        let value = self.data;

        let mut curr_val_offset = 0;
        let mut curr_jentry_encoded = 0;
        let mut curr_jentry: Option<JEntry> = None;

        for path in keypaths {
            if let Some(ref jentry) = curr_jentry {
                if jentry.type_code != CONTAINER_TAG {
                    return Ok(None);
                }
            }
            let header = read_u32(value, curr_val_offset)?;
            let length = (header & CONTAINER_HEADER_LEN_MASK) as i32;
            match (path, header & CONTAINER_HEADER_TYPE_MASK) {
                (KeyPath::QuotedName(name) | KeyPath::Name(name), OBJECT_CONTAINER_TAG) => {
                    match get_jentry_by_name(value, curr_val_offset, header, name, false) {
                        Some((jentry, encoded, value_offset)) => {
                            curr_jentry_encoded = encoded;
                            curr_jentry = Some(jentry);
                            curr_val_offset = value_offset;
                        }
                        None => return Ok(None),
                    };
                }
                (KeyPath::Index(idx), ARRAY_CONTAINER_TAG) => {
                    if *idx > length || length + *idx < 0 {
                        return Ok(None);
                    } else {
                        let idx = if *idx >= 0 {
                            *idx as usize
                        } else {
                            (length + *idx) as usize
                        };
                        match get_jentry_by_index(value, curr_val_offset, header, idx) {
                            Some((jentry, encoded, value_offset)) => {
                                curr_jentry_encoded = encoded;
                                curr_jentry = Some(jentry);
                                curr_val_offset = value_offset;
                            }
                            None => return Ok(None),
                        }
                    }
                }
                (_, _) => return Ok(None),
            }
        }
        // If the key paths is empty, return original value.
        if curr_val_offset == 0 {
            return Ok(Some(OwnedJsonb::new(value.to_vec())));
        }
        let val = curr_jentry.map(|jentry| {
            let val_data = extract_by_jentry(&jentry, curr_jentry_encoded, curr_val_offset, value);
            OwnedJsonb::new(val_data)
        });
        Ok(val)
    }

    /// Traverses the JSONB value and checks string values against a provided function.
    ///
    /// This function recursively traverses the JSONB value, visiting all string elements.
    /// For each string element, it calls the provided `func`.  If `func` returns `true` for any string element,
    /// the traversal stops, and the function returns `Ok(true)`. If `func` returns `false` for all string elements,
    /// the traversal completes, and the function returns `Ok(false)`.
    ///
    /// This function is useful for efficiently searching for a specific string within a potentially complex JSONB structure
    /// without having to manually traverse the entire structure.
    ///
    /// # Arguments
    ///
    /// * `func` - A function that takes a byte slice (`&[u8]`) representing a string value and returns a boolean indicating whether the string satisfies a certain condition.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If `func` returns `true` for any string element encountered during traversal.
    /// * `Ok(false)` - If `func` returns `false` for all string elements.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let jsonb_value = r#"{"a": "hello", "b": [1, "world", {"c": "rust"}]}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    ///
    /// // Check if any string contains "rust"
    /// let contains_rust = raw_jsonb.traverse_check_string(|s| s.eq("rust".as_bytes())).unwrap();
    /// assert!(contains_rust);
    ///
    /// // Check if any string contains "xyz"
    /// let contains_xyz = raw_jsonb.traverse_check_string(|s| s.eq("xyz".as_bytes())).unwrap();
    /// assert!(!contains_xyz);
    ///
    /// // Check if any string is longer than 5 characters
    /// let long_string = raw_jsonb.traverse_check_string(|s| s.len() > 5).unwrap();
    /// assert!(!long_string);
    ///
    /// // Example with an array of strings
    /// let jsonb_value = r#"["hello", "world", "rust"]"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let contains_rust = raw_jsonb.traverse_check_string(|s| s.eq("rust".as_bytes())).unwrap();
    /// assert!(contains_rust);
    /// ```
    pub fn traverse_check_string(&self, func: impl Fn(&[u8]) -> bool) -> Result<bool, Error> {
        let value = self.data;
        let mut offsets = VecDeque::new();
        offsets.push_back(0);

        while let Some(offset) = offsets.pop_front() {
            let header = read_u32(value, offset)?;
            let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;

            let size = match header & CONTAINER_HEADER_TYPE_MASK {
                SCALAR_CONTAINER_TAG => 1,
                ARRAY_CONTAINER_TAG => length,
                OBJECT_CONTAINER_TAG => length * 2,
                _ => {
                    return Err(Error::InvalidJsonb);
                }
            };

            let mut jentry_offset = offset + 4;
            let mut val_offset = offset + 4 + 4 * size;
            for _ in 0..size {
                let encoded = read_u32(value, jentry_offset)?;
                let jentry = JEntry::decode_jentry(encoded);
                match jentry.type_code {
                    CONTAINER_TAG => {
                        offsets.push_back(val_offset);
                    }
                    STRING_TAG => {
                        let val_length = jentry.length as usize;
                        if func(&value[val_offset..val_offset + val_length]) {
                            return Ok(true);
                        }
                    }
                    _ => {}
                }
                jentry_offset += 4;
                val_offset += jentry.length as usize;
            }
        }
        Ok(false)
    }

    /// Checks if all specified keys exist in a JSONB object.
    ///
    /// This function checks if a JSONB object contains *all* of the keys provided in the `keys` iterator.
    /// The keys are expected to be UTF-8 encoded byte slices. If the JSONB value is not an object,
    /// the function will return `Ok(false)`.
    ///
    /// # Arguments
    ///
    /// * `keys` - An iterator of byte slices representing the keys to check for.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If all keys exist in the JSONB object.
    /// * `Ok(false)` - If any of the keys do not exist in the object, if any key is not valid UTF-8, or if the JSONB value is not an object.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data other than the value not being an object).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": 2, "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    ///
    /// let keys = ["a".as_bytes(), "b".as_bytes(), "c".as_bytes()];
    /// assert!(raw_jsonb.exists_all_keys(keys.into_iter()).unwrap());
    ///
    /// let keys = ["b".as_bytes(), "b".as_bytes(), "d".as_bytes()];
    /// assert!(!raw_jsonb.exists_all_keys(keys.into_iter()).unwrap()); // "d" does not exist
    ///
    /// let keys = ["a".as_bytes(), "b".as_bytes(), &[0xff_u8]];  // Invalid UTF-8
    /// assert!(!raw_jsonb.exists_all_keys(keys.into_iter()).unwrap());
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let keys = ["a".as_bytes()];
    /// assert!(!raw_jsonb.exists_all_keys(keys.into_iter()).unwrap()); // Not an object
    ///
    /// let obj_jsonb = r#"{"a b": 1, "c": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let keys = ["a b".as_bytes(), "c".as_bytes()];
    /// assert!(raw_jsonb.exists_all_keys(keys.into_iter()).unwrap());
    /// ```
    pub fn exists_all_keys<'a, I: Iterator<Item = &'a [u8]>>(
        &self,
        keys: I,
    ) -> Result<bool, Error> {
        let value = self.data;
        let header = read_u32(value, 0)?;

        for key in keys {
            match from_utf8(key) {
                Ok(key) => {
                    if !Self::exists_key(value, header, key)? {
                        return Ok(false);
                    }
                }
                Err(_) => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Checks if any of the specified keys exist in a JSONB object.
    ///
    /// This function checks if a JSONB object contains *any* of the keys provided in the `keys` iterator.
    /// The keys are expected to be UTF-8 encoded byte slices.
    /// If the JSONB value is not an object, the function will return `Ok(false)`.
    ///
    /// # Arguments
    ///
    /// * `keys` - An iterator of byte slices representing the keys to check for.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If any of the keys exist in the JSONB object.
    /// * `Ok(false)` - If none of the keys exist in the object, if any key is not valid UTF-8, or if the JSONB value is not an object.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data other than the value not being an object).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": 2, "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    ///
    /// let keys = ["a".as_bytes(), "d".as_bytes(), "e".as_bytes()];
    /// assert!(raw_jsonb.exists_any_keys(keys.into_iter()).unwrap()); // "a" exists
    ///
    /// let keys = ["d".as_bytes(), "e".as_bytes(), "f".as_bytes()];
    /// assert!(!raw_jsonb.exists_any_keys(keys.into_iter()).unwrap()); // None of the keys exist
    ///
    /// let keys = ["d".as_bytes(), &[0xff_u8], "f".as_bytes()]; // Invalid UTF-8 for the second key
    /// assert!(!raw_jsonb.exists_any_keys(keys.into_iter()).unwrap()); // Stops at invalid UTF-8 and returns false
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let keys = ["a".as_bytes()];
    /// assert!(!raw_jsonb.exists_any_keys(keys.into_iter()).unwrap()); // Not an object
    ///
    /// let obj_jsonb = r#"{"a b": 1, "c": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let keys = ["a b".as_bytes()];
    /// assert!(raw_jsonb.exists_any_keys(keys.into_iter()).unwrap());
    /// ```
    pub fn exists_any_keys<'a, I: Iterator<Item = &'a [u8]>>(
        &self,
        keys: I,
    ) -> Result<bool, Error> {
        let value = self.data;
        let header = read_u32(value, 0)?;

        for key in keys {
            if let Ok(key) = from_utf8(key) {
                if Self::exists_key(value, header, key)? {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn exists_key(value: &[u8], header: u32, key: &str) -> Result<bool, Error> {
        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {
                let mut matches = false;
                for obj_key in iteate_object_keys(value, header) {
                    if obj_key.eq(key) {
                        matches = true;
                        break;
                    }
                }
                Ok(matches)
            }
            ARRAY_CONTAINER_TAG => {
                let mut matches = false;
                for (jentry, val) in iterate_array(value, header) {
                    if jentry.type_code != STRING_TAG {
                        continue;
                    }
                    let val = unsafe { from_utf8_unchecked(val) };
                    if val.eq(key) {
                        matches = true;
                        break;
                    }
                }
                Ok(matches)
            }
            SCALAR_CONTAINER_TAG => Ok(false),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Concatenates two JSONB values.
    ///
    /// This function concatenates the `self` JSONB value with the `other` JSONB value.
    /// The concatenation behavior depends on the types of the input values:
    ///
    /// * **Object + Object:** Merges the two objects. If there are duplicate keys, the keys from the `other` object will overwrite the keys from the `self` object.
    /// * **Array + Array:** Appends the elements of the `other` array to the `self` array.
    /// * **Object/Scalar + Array:** Creates a new array containing the `self` value (as a single element) followed by the elements of the `other` array.
    /// * **Array + Object/Scalar:** Creates a new array containing the elements of the `self` array followed by the `other` value (as a single element).
    /// * **Object + Scalar:** Creates a new array containing the `self` object (as a single element) and the `other` scalar (as a single element).
    /// * **Scalar + Object:** Creates a new array containing the `self` scalar (as a single element) and the `other` object (as a single element).
    /// * **Scalar + Scalar:** Creates a new array containing both scalar values as elements.
    ///
    /// If the input JSONB values are invalid or if an unsupported concatenation is attempted (e.g. trying to concatenate a number with an object directly, without creating an array), an error is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The first JSONB value.
    /// * `other` - The second JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The concatenated JSONB value.
    /// * `Err(Error)` - If the input JSONB values are invalid, or if an unsupported concatenation is attempted.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Object + Object
    /// let obj1 = r#"{"a": 1, "b": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"b": 3, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let concatenated = obj1.as_raw().concat(&obj2.as_raw()).unwrap();
    /// assert_eq!(concatenated.to_string(), r#"{"a":1,"b":3,"c":4}"#);  // "b" is overwritten
    ///
    /// // Array + Array
    /// let arr1 = "[1, 2]".parse::<OwnedJsonb>().unwrap();
    /// let arr2 = "[3, 4]".parse::<OwnedJsonb>().unwrap();
    /// let concatenated = arr1.as_raw().concat(&arr2.as_raw()).unwrap();
    /// assert_eq!(concatenated.to_string(), "[1,2,3,4]");
    ///
    /// // Object + Array
    /// let obj = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let arr = "[2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let concatenated = obj.as_raw().concat(&arr.as_raw()).unwrap();
    /// assert_eq!(concatenated.to_string(), r#"[{"a":1},2,3]"#);
    ///
    /// // Scalar + Array
    /// let scalar = "1".parse::<OwnedJsonb>().unwrap();
    /// let arr = "[2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let concatenated = scalar.as_raw().concat(&arr.as_raw()).unwrap();
    /// assert_eq!(concatenated.to_string(), "[1,2,3]");
    ///
    /// // Scalar + Scalar
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "2".parse::<OwnedJsonb>().unwrap();
    /// let concatenated = scalar1.as_raw().concat(&scalar2.as_raw()).unwrap();
    /// assert_eq!(concatenated.to_string(), "[1,2]");
    /// ```
    pub fn concat(&self, other: &RawJsonb) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let left = self.data;
        let right = other.data;

        let left_header = read_u32(left, 0)?;
        let right_header = read_u32(right, 0)?;

        let left_len = (left_header & CONTAINER_HEADER_LEN_MASK) as usize;
        let right_len = (right_header & CONTAINER_HEADER_LEN_MASK) as usize;

        let left_type = left_header & CONTAINER_HEADER_TYPE_MASK;
        let right_type = right_header & CONTAINER_HEADER_TYPE_MASK;

        match (left_type, right_type) {
            (OBJECT_CONTAINER_TAG, OBJECT_CONTAINER_TAG) => {
                let mut builder = ObjectBuilder::new();
                for (key, jentry, item) in iterate_object_entries(left, left_header) {
                    builder.push_raw(key, jentry, item);
                }
                for (key, jentry, item) in iterate_object_entries(right, right_header) {
                    builder.push_raw(key, jentry, item);
                }
                builder.build_into(&mut buf);
            }
            (ARRAY_CONTAINER_TAG, ARRAY_CONTAINER_TAG) => {
                let mut builder = ArrayBuilder::new(left_len + right_len);
                for (jentry, item) in iterate_array(left, left_header) {
                    builder.push_raw(jentry, item);
                }
                for (jentry, item) in iterate_array(right, right_header) {
                    builder.push_raw(jentry, item);
                }
                builder.build_into(&mut buf);
            }
            (OBJECT_CONTAINER_TAG | SCALAR_CONTAINER_TAG, ARRAY_CONTAINER_TAG) => {
                let mut builder = ArrayBuilder::new(right_len + 1);
                match left_type {
                    OBJECT_CONTAINER_TAG => {
                        let jentry = JEntry::make_container_jentry(left.len());
                        builder.push_raw(jentry, left);
                    }
                    _ => {
                        let jentry = JEntry::decode_jentry(read_u32(left, 4)?);
                        builder.push_raw(jentry, &left[8..]);
                    }
                };
                for (jentry, item) in iterate_array(right, right_header) {
                    builder.push_raw(jentry, item);
                }
                builder.build_into(&mut buf);
            }
            (ARRAY_CONTAINER_TAG, OBJECT_CONTAINER_TAG | SCALAR_CONTAINER_TAG) => {
                let mut builder = ArrayBuilder::new(left_len + 1);
                for (jentry, item) in iterate_array(left, left_header) {
                    builder.push_raw(jentry, item);
                }
                match right_type {
                    OBJECT_CONTAINER_TAG => {
                        let jentry = JEntry::make_container_jentry(right.len());
                        builder.push_raw(jentry, right);
                    }
                    _ => {
                        let jentry = JEntry::decode_jentry(read_u32(right, 4)?);
                        builder.push_raw(jentry, &right[8..]);
                    }
                };
                builder.build_into(&mut buf);
            }
            (OBJECT_CONTAINER_TAG, SCALAR_CONTAINER_TAG) => {
                let mut builder = ArrayBuilder::new(2);
                let jentry = JEntry::make_container_jentry(left.len());
                builder.push_raw(jentry, left);
                let jentry = JEntry::decode_jentry(read_u32(right, 4)?);
                builder.push_raw(jentry, &right[8..]);
                builder.build_into(&mut buf);
            }
            (SCALAR_CONTAINER_TAG, OBJECT_CONTAINER_TAG) => {
                let mut builder = ArrayBuilder::new(2);
                let jentry = JEntry::decode_jentry(read_u32(left, 4)?);
                builder.push_raw(jentry, &left[8..]);
                let jentry = JEntry::make_container_jentry(right.len());
                builder.push_raw(jentry, right);
                builder.build_into(&mut buf);
            }
            (SCALAR_CONTAINER_TAG, SCALAR_CONTAINER_TAG) => {
                let mut builder = ArrayBuilder::new(2);
                let jentry = JEntry::decode_jentry(read_u32(left, 4)?);
                builder.push_raw(jentry, &left[8..]);
                let jentry = JEntry::decode_jentry(read_u32(right, 4)?);
                builder.push_raw(jentry, &right[8..]);
                builder.build_into(&mut buf);
            }
            (_, _) => {
                return Err(Error::InvalidJsonb);
            }
        }
        Ok(OwnedJsonb::new(buf))
    }

    /// Recursively reomves all object key-value pairs that have null values from a JSONB object.
    ///
    /// Note: null values in the JSONB array are not reomved.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The JSONB value with nulls removed.
    /// * `Err(Error)` - If the input JSONB value is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Object with nulls
    /// let obj_with_nulls = r#"{"a": 1, "b": null, "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let stripped = obj_with_nulls.as_raw().strip_nulls().unwrap();
    /// assert_eq!(stripped.to_string(), r#"{"a":1,"c":3}"#);
    ///
    /// // Nested structures
    /// let nested = r#"{"a": [1, null, {"b": null, "c": 2}]}"#.parse::<OwnedJsonb>().unwrap();
    /// let stripped = nested.as_raw().strip_nulls().unwrap();
    /// assert_eq!(stripped.to_string(), r#"{"a":[1,null,{"c":2}]}"#);
    ///
    /// // Array with nulls
    /// let arr_with_nulls = r#"[1, null, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let stripped = arr_with_nulls.as_raw().strip_nulls().unwrap();
    /// assert_eq!(stripped.to_string(), r#"[1,null,3]"#); // Remains unchanged
    ///
    /// // Scalar null
    /// let null_scalar = "null".parse::<OwnedJsonb>().unwrap();
    /// let stripped = null_scalar.as_raw().strip_nulls().unwrap();
    /// assert_eq!(stripped.to_string(), "null"); // Remains unchanged
    /// ```
    pub fn strip_nulls(&self) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let value = self.data;
        let header = read_u32(value, 0)?;

        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {
                let builder = Self::strip_nulls_object(header, value)?;
                builder.build_into(&mut buf);
            }
            ARRAY_CONTAINER_TAG => {
                let builder = Self::strip_nulls_array(header, value)?;
                builder.build_into(&mut buf);
            }
            SCALAR_CONTAINER_TAG => buf.extend_from_slice(value),
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }
        Ok(OwnedJsonb::new(buf))
    }

    fn strip_nulls_array(header: u32, value: &[u8]) -> Result<ArrayBuilder<'_>, Error> {
        let len = (header & CONTAINER_HEADER_LEN_MASK) as usize;
        let mut builder = ArrayBuilder::new(len);

        for (jentry, item) in iterate_array(value, header) {
            match jentry.type_code {
                CONTAINER_TAG => {
                    let item_header = read_u32(item, 0)?;
                    match item_header & CONTAINER_HEADER_TYPE_MASK {
                        OBJECT_CONTAINER_TAG => {
                            builder.push_object(Self::strip_nulls_object(item_header, item)?);
                        }
                        ARRAY_CONTAINER_TAG => {
                            builder.push_array(Self::strip_nulls_array(item_header, item)?);
                        }
                        _ => {
                            return Err(Error::InvalidJsonb);
                        }
                    }
                }
                NULL_TAG | STRING_TAG | NUMBER_TAG | FALSE_TAG | TRUE_TAG => {
                    builder.push_raw(jentry, item)
                }
                _ => {
                    return Err(Error::InvalidJsonb);
                }
            }
        }
        Ok(builder)
    }

    fn strip_nulls_object(header: u32, value: &[u8]) -> Result<ObjectBuilder<'_>, Error> {
        let mut builder = ObjectBuilder::new();
        for (key, jentry, item) in iterate_object_entries(value, header) {
            match jentry.type_code {
                CONTAINER_TAG => {
                    let item_header = read_u32(item, 0)?;
                    match item_header & CONTAINER_HEADER_TYPE_MASK {
                        OBJECT_CONTAINER_TAG => {
                            builder.push_object(key, Self::strip_nulls_object(item_header, item)?);
                        }
                        ARRAY_CONTAINER_TAG => {
                            builder.push_array(key, Self::strip_nulls_array(item_header, item)?);
                        }
                        _ => {
                            return Err(Error::InvalidJsonb);
                        }
                    }
                }
                NULL_TAG => continue,
                STRING_TAG | NUMBER_TAG | FALSE_TAG | TRUE_TAG => {
                    builder.push_raw(key, jentry, item)
                }
                _ => {
                    return Err(Error::InvalidJsonb);
                }
            }
        }
        Ok(builder)
    }

    /// Deletes a key-value pair from a JSONB object or an element from a JSONB array.
    ///
    /// This function removes a key-value pair from a JSONB object if the key matches the given `name`
    /// or removes an element from a JSONB array if the element is a string that matches the given `name`.
    ///
    /// * **Object:** If the input is an object, the key-value pair with the matching key is removed.  The key comparison is case-sensitive.
    /// * **Array:** If the input is an array, elements that are strings and match `name` (case-sensitive) are removed.  Other array elements remain unchanged.
    /// * **Invalid input:** If the input JSONB value is a scalar value, an `Error::InvalidJsonType` is returned. Other invalid JSONB data results in an `Error::InvalidJsonb`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    /// * `name` - The key (for objects) or string value (for arrays) to match.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The modified JSONB value with the matching key-value pair or element removed.
    /// * `Err(Error)` - If the input JSONB value is a scalar, or if the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Deleting from an object
    /// let obj_jsonb = r#"{"a": 1, "b": "hello", "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let deleted = raw_jsonb.delete_by_name("b").unwrap();
    /// assert_eq!(deleted.to_string(), r#"{"a":1,"c":3}"#);
    ///
    /// // Deleting from an array (string elements only)
    /// let arr_jsonb = r#"[1, "hello", 3, "world"]"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let deleted = raw_jsonb.delete_by_name("hello").unwrap();
    /// assert_eq!(deleted.to_string(), "[1,3,\"world\"]");
    ///
    /// // Non-matching key in object
    /// let deleted = raw_jsonb.delete_by_name("x").unwrap(); // "x" doesn't exist
    /// assert_eq!(deleted.to_string(), r#"[1,"hello",3,"world"]"#); // Original array returned
    ///
    /// // Non-matching value in array
    /// let deleted = arr_jsonb.as_raw().delete_by_name("xyz").unwrap(); // "xyz" doesn't exist
    /// assert_eq!(deleted.to_string(), r#"[1,"hello",3,"world"]"#); // Original array returned
    ///
    /// // Attempting to delete from a scalar
    /// let scalar_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = scalar_jsonb.as_raw();
    /// let result = raw_jsonb.delete_by_name("a");
    /// assert!(result.is_err()); // Returns an error
    /// ```
    pub fn delete_by_name(&self, name: &str) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let value = self.data;
        let header = read_u32(value, 0)?;

        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {
                let mut builder = ObjectBuilder::new();
                for (key, jentry, item) in iterate_object_entries(value, header) {
                    if !key.eq(name) {
                        builder.push_raw(key, jentry, item);
                    }
                }
                builder.build_into(&mut buf);
            }
            ARRAY_CONTAINER_TAG => {
                let mut builder = ArrayBuilder::new((header & CONTAINER_HEADER_LEN_MASK) as usize);
                for (jentry, item) in iterate_array(value, header) {
                    let matches = match jentry.type_code {
                        STRING_TAG => {
                            let v = unsafe { from_utf8_unchecked(item) };
                            v.eq(name)
                        }
                        _ => false,
                    };
                    if !matches {
                        builder.push_raw(jentry, item);
                    }
                }
                builder.build_into(&mut buf);
            }
            SCALAR_CONTAINER_TAG => return Err(Error::InvalidJsonType),
            _ => return Err(Error::InvalidJsonb),
        }
        Ok(OwnedJsonb::new(buf))
    }

    /// Deletes the element at the specified index from a JSONB array.
    ///
    /// This function removes the element at the given `index` from a JSONB array.
    /// The `index` can be positive or negative:
    ///
    /// * **Positive index:**  0-based index from the beginning of the array.
    /// * **Negative index:**  1-based index from the end of the array (e.g., -1 refers to the last element).
    ///
    /// If the `index` is out of bounds, the original JSONB array is returned unchanged.
    /// If the input JSONB value is not an array (e.g., it's an object or a scalar), an `Error::InvalidJsonType` is returned.
    /// Other invalid JSONB data results in an `Error::InvalidJsonb`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    /// * `index` - The index of the element to delete.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The JSONB array with the element at the specified index removed, or the original array if the index is out of bounds.
    /// * `Err(Error)` - If the input JSONB value is not an array, or if the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let arr_jsonb = r#"[1, "hello", 3, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    ///
    /// // Delete element at index 1
    /// let deleted = raw_jsonb.delete_by_index(1).unwrap();
    /// assert_eq!(deleted.to_string(), "[1,3,4]");
    ///
    /// // Delete last element using negative index
    /// let deleted = raw_jsonb.delete_by_index(-1).unwrap();
    /// assert_eq!(deleted.to_string(), "[1,\"hello\",3]");
    ///
    /// // Out of bounds index (positive)
    /// let deleted = raw_jsonb.delete_by_index(4).unwrap();
    /// assert_eq!(deleted.to_string(), "[1,\"hello\",3,4]"); // Original array returned
    ///
    /// // Out of bounds index (negative)
    /// let deleted = raw_jsonb.delete_by_index(-5).unwrap();
    /// assert_eq!(deleted.to_string(), "[1,\"hello\",3,4]"); // Original array returned
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let result = raw_jsonb.delete_by_index(0);
    /// assert!(result.is_err()); // Error because input is not an array
    pub fn delete_by_index(&self, index: i32) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let value = self.data;
        let header = read_u32(value, 0)?;

        match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                let len = (header & CONTAINER_HEADER_LEN_MASK) as i32;
                let index = if index < 0 { len - index.abs() } else { index };
                if index < 0 || index >= len {
                    buf.extend_from_slice(value);
                } else {
                    let mut builder =
                        ArrayBuilder::new((header & CONTAINER_HEADER_LEN_MASK) as usize);
                    let index = index as usize;
                    for (i, entry) in iterate_array(value, header).enumerate() {
                        if i != index {
                            builder.push_raw(entry.0, entry.1);
                        }
                    }
                    builder.build_into(&mut buf);
                }
            }
            SCALAR_CONTAINER_TAG | OBJECT_CONTAINER_TAG => return Err(Error::InvalidJsonType),
            _ => return Err(Error::InvalidJsonb),
        }
        Ok(OwnedJsonb::new(buf))
    }

    /// Inserts a new element into a JSONB array at the specified position.
    ///
    /// This function inserts the `new_val` into the JSONB array at the position specified by `pos`.  The `pos` parameter can be positive or negative:
    ///
    /// * **Positive index:** 0-based index from the beginning of the array.
    /// * **Negative index:** 1-based index from the end of the array (e.g., -1 refers to the last element).
    ///
    /// If `pos` is less than 0, the element is inserted at the beginning of the array. If `pos` is greater than or equal to the length of the array, the element is appended to the end.  If the input JSONB value is not an array, object or scalar, an error is returned (`Error::InvalidJsonb`). If the input is an object or scalar, it's treated as a single element array.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB array.
    /// * `pos` - The position at which to insert the new element (positive or negative index).
    /// * `new_val` - The new element to insert.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The modified JSONB array with the new element inserted.
    /// * `Err(Error)` - If the input JSONB value is not an array or if the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let new_jsonb = "4".parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    ///
    /// // Insert at index 1
    /// let inserted = raw_jsonb.array_insert(1, new_raw_jsonb).unwrap();
    /// assert_eq!(inserted.to_string(), "[1,4,2,3]");
    ///
    /// // Insert at the beginning (pos = 0)
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.array_insert(0, new_raw_jsonb).unwrap();
    /// assert_eq!(inserted.to_string(), "[4,1,2,3]");
    ///
    /// // Insert at the end (pos >= length)
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.array_insert(10, new_raw_jsonb).unwrap();
    /// assert_eq!(inserted.to_string(), "[1,2,3,4]");
    ///
    /// // Insert into an object
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let new_jsonb = "2".parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.array_insert(0, new_raw_jsonb);
    /// assert_eq!(inserted.unwrap().to_string(), r#"[2,{"a":1}]"#);
    ///
    /// // Insert into a scalar
    /// let scalar_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = scalar_jsonb.as_raw();
    /// let new_jsonb = "2".parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.array_insert(0, new_raw_jsonb);
    /// assert_eq!(inserted.unwrap().to_string(), "[2,1]");
    /// ```
    pub fn array_insert(&self, pos: i32, new_val: RawJsonb) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let value = self.data;
        let new_value = new_val.data;
        let header = read_u32(value, 0)?;
        let len = match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => (header & CONTAINER_HEADER_LEN_MASK) as i32,
            SCALAR_CONTAINER_TAG | OBJECT_CONTAINER_TAG => 1,
            _ => {
                return Err(Error::InvalidJsonb);
            }
        };

        let idx = if pos < 0 { len - pos.abs() } else { pos };
        let idx = if idx < 0 {
            0
        } else if idx > len {
            len
        } else {
            idx
        } as usize;
        let len = len as usize;

        let mut items = VecDeque::with_capacity(len);
        match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                for (jentry, item) in iterate_array(value, header) {
                    items.push_back((jentry, item));
                }
            }
            OBJECT_CONTAINER_TAG => {
                let jentry = JEntry::make_container_jentry(value.len());
                items.push_back((jentry, value));
            }
            _ => {
                let encoded = read_u32(value, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                items.push_back((jentry, &value[8..]));
            }
        }

        let mut builder = ArrayBuilder::new(len + 1);
        if idx > 0 {
            let mut i = 0;
            while let Some((jentry, item)) = items.pop_front() {
                builder.push_raw(jentry, item);
                i += 1;
                if i >= idx {
                    break;
                }
            }
        }

        let new_header = read_u32(new_value, 0)?;
        match new_header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG => {
                let new_jentry = JEntry::make_container_jentry(new_value.len());
                builder.push_raw(new_jentry, new_value);
            }
            _ => {
                let encoded = read_u32(new_value, 4)?;
                let new_jentry = JEntry::decode_jentry(encoded);
                builder.push_raw(new_jentry, &new_value[8..]);
            }
        }

        while let Some((jentry, item)) = items.pop_front() {
            builder.push_raw(jentry, item);
        }
        builder.build_into(&mut buf);

        Ok(OwnedJsonb::new(buf))
    }

    /// Returns a JSONB array with duplicate elements removed.
    ///
    /// This function takes a JSONB value as input and returns a new JSONB array containing only the unique elements from the input.
    /// The behavior depends on the input type:
    ///
    /// * **Array:** Returns a new array containing only the unique elements from the input array.  The order of elements in the output array is not guaranteed to be the same as the input array.
    /// * **Object:** Returns a new array containing the original object as its only element.
    /// * **Scalar:** Returns a new array containing the original scalar value as its only element.
    /// * **Invalid JSONB:** Returns an error.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - A JSONB array containing only the unique elements from the input.
    /// * `Err(Error)` - If the input JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Array with duplicates
    /// let arr_jsonb = r#"[1, 2, 2, 3, 1, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// let distinct = arr_jsonb.as_raw().array_distinct().unwrap();
    /// assert_eq!(distinct.to_string(), "[1,2,3,4]"); // Order may vary
    ///
    /// // Array with only unique elements
    /// let arr_jsonb = r#"[1, 2, 3, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// let distinct = arr_jsonb.as_raw().array_distinct().unwrap();
    /// assert_eq!(distinct.to_string(), "[1,2,3,4]"); // Order may vary
    ///
    /// // Object
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let distinct = obj_jsonb.as_raw().array_distinct().unwrap();
    /// assert_eq!(distinct.to_string(), r#"[{"a":1}]"#);
    ///
    /// // Scalar
    /// let scalar_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let distinct = scalar_jsonb.as_raw().array_distinct().unwrap();
    /// assert_eq!(distinct.to_string(), "[1]");
    ///
    /// // Invalid JSONB data
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.array_distinct();
    /// assert!(result.is_err());
    /// ```
    pub fn array_distinct(&self) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let value = self.data;
        let header = read_u32(value, 0)?;
        let mut builder = ArrayBuilder::new(0);
        match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                let mut item_set = BTreeSet::new();
                for (jentry, item) in iterate_array(value, header) {
                    if !item_set.contains(&(jentry.clone(), item)) {
                        item_set.insert((jentry.clone(), item));
                        builder.push_raw(jentry, item);
                    }
                }
            }
            OBJECT_CONTAINER_TAG => {
                let jentry = JEntry::make_container_jentry(value.len());
                builder.push_raw(jentry, value);
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(value, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                builder.push_raw(jentry, &value[8..]);
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }
        builder.build_into(&mut buf);

        Ok(OwnedJsonb::new(buf))
    }

    /// Computes the intersection of two JSONB arrays or the containment check for objects and scalars.
    ///
    /// This function calculates the intersection of two JSONB arrays or checks if one JSONB value is contained within another.
    /// The behavior depends on the input types:
    ///
    /// * **Array + Array:** Returns a new array containing only the elements that are present in *both* input arrays.  The order of elements is not guaranteed.  Duplicate elements are handled correctly; the multiplicity of elements in the intersection is the minimum of their multiplicities in the input arrays.
    /// * **Object/Scalar + Object/Scalar:** Returns a new array containing the `self` value only if it's present in the `other` value. This effectively checks for containment. The contained value must be completely equal to the other value, including any nested structures. For arrays, this containment check would require a recursive check for each element in both arrays.
    /// * **Invalid input:** Returns an error if either input is not an array, object, or scalar.
    ///
    /// # Arguments
    ///
    /// * `self` - The first JSONB value.
    /// * `other` - The second JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The intersection array (for array + array) or a single-element array indicating containment (for other combinations). The empty array `[]` indicates that there's no intersection or containment.
    /// * `Err(Error)` - If the input JSONB data is invalid or if the input types are incompatible (e.g., trying to find the intersection of an array and an object).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Array intersection
    /// let arr1 = r#"[1, 2, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[2, 3, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// let intersection = arr1.as_raw().array_intersection(arr2.as_raw()).unwrap();
    /// assert_eq!(intersection.to_string(), "[2,3]"); // Order may vary, duplicates handled
    ///
    /// let arr1 = r#"[1, 1, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[1, 1, 1, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let intersection = arr1.as_raw().array_intersection(arr2.as_raw()).unwrap();
    /// assert_eq!(intersection.to_string(), "[1,1,3]"); //Order may vary
    ///
    /// // Object containment (checks for complete equality)
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let contained = obj1.as_raw().array_intersection(obj2.as_raw()).unwrap();
    /// assert_eq!(contained.to_string(), r#"[{"a":1}]"#);
    ///
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// let contained = obj1.as_raw().array_intersection(obj2.as_raw()).unwrap();
    /// assert_eq!(contained.to_string(), "[]"); // Not contained
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "1".parse::<OwnedJsonb>().unwrap();
    /// let contained = scalar1.as_raw().array_intersection(scalar2.as_raw()).unwrap();
    /// assert_eq!(contained.to_string(), "[1]"); // Contained
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "2".parse::<OwnedJsonb>().unwrap();
    /// let contained = scalar1.as_raw().array_intersection(scalar2.as_raw()).unwrap();
    /// assert_eq!(contained.to_string(), "[]"); // Not contained
    /// ```
    pub fn array_intersection(&self, other: RawJsonb) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let left = self.data;
        let right = other.data;

        let left_header = read_u32(left, 0)?;
        let right_header = read_u32(right, 0)?;

        let mut item_map = BTreeMap::new();
        match right_header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                for (jentry, item) in iterate_array(right, right_header) {
                    if let Some(cnt) = item_map.get_mut(&(jentry.clone(), item)) {
                        *cnt += 1;
                    } else {
                        item_map.insert((jentry, item), 1);
                    }
                }
            }
            OBJECT_CONTAINER_TAG => {
                let jentry = JEntry::make_container_jentry(right.len());
                item_map.insert((jentry, right), 1);
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(right, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                item_map.insert((jentry, &right[8..]), 1);
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }

        let mut builder = ArrayBuilder::new(0);
        match left_header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                for (jentry, item) in iterate_array(left, left_header) {
                    if let Some(cnt) = item_map.get_mut(&(jentry.clone(), item)) {
                        if *cnt > 0 {
                            *cnt -= 1;
                            builder.push_raw(jentry, item);
                        }
                    }
                }
            }
            OBJECT_CONTAINER_TAG => {
                let jentry = JEntry::make_container_jentry(left.len());
                if item_map.contains_key(&(jentry.clone(), left)) {
                    builder.push_raw(jentry, left);
                }
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(left, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                if item_map.contains_key(&(jentry.clone(), &left[8..])) {
                    builder.push_raw(jentry, &left[8..]);
                }
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }
        builder.build_into(&mut buf);

        Ok(OwnedJsonb::new(buf))
    }

    /// Computes the set difference between two JSONB arrays or checks for non-containment of objects and scalars.
    ///
    /// This function calculates the set difference between two JSONB arrays or checks if one JSONB value is *not* contained within another.  The behavior depends on the input types:
    ///
    /// * **Array + Array:** Returns a new array containing only the elements that are present in the `self` array but *not* in the `other` array. The order of elements is not guaranteed. Duplicate elements are handled correctly; if an element appears multiple times in `self` but is present in `other`, it will be removed from the result only up to the number of times it appears in `other`.
    /// * **Object/Scalar + Object/Scalar:** Returns a new array containing the `self` value if it's *not* contained in the `other` value. This effectively checks for non-containment. For arrays, this non-containment check would require a recursive check for each element in both arrays.  Complete equality is required for containment; even a slight difference (e.g., a different number of duplicate elements) means the value is not contained.
    /// * **Invalid input:** Returns an error if either input is not an array, object, or scalar.
    ///
    /// # Arguments
    ///
    /// * `self` - The first JSONB value.
    /// * `other` - The second JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The resulting array after removing elements from `self` that are present in `other` (for array + array), or a single-element array indicating non-containment (for other combinations). An empty array `[]` indicates that all elements of `self` are present in `other`.
    /// * `Err(Error)` - If the input JSONB data is invalid or if the input types are incompatible (e.g., trying to find the set difference between an array and an object).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Array except
    /// let arr1 = r#"[1, 2, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[2, 3, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// let except = arr1.as_raw().array_except(arr2.as_raw()).unwrap();
    /// assert_eq!(except.to_string(), "[1,2]"); // Order may vary, duplicates handled
    ///
    /// let arr1 = r#"[1, 1, 2, 3, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[1, 3, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let except = arr1.as_raw().array_except(arr2.as_raw()).unwrap();
    /// assert_eq!(except.to_string(), "[1,2]"); // Order may vary
    ///
    /// // Object non-containment
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let not_contained = obj1.as_raw().array_except(obj2.as_raw()).unwrap();
    /// assert_eq!(not_contained.to_string(), "[]"); // Completely contained
    ///
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// let not_contained = obj1.as_raw().array_except(obj2.as_raw()).unwrap();
    /// assert_eq!(not_contained.to_string(), r#"[{"a":1}]"#); // Not contained
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "1".parse::<OwnedJsonb>().unwrap();
    /// let not_contained = scalar1.as_raw().array_except(scalar2.as_raw()).unwrap();
    /// assert_eq!(not_contained.to_string(), "[]"); // Contained
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "2".parse::<OwnedJsonb>().unwrap();
    /// let not_contained = scalar1.as_raw().array_except(scalar2.as_raw()).unwrap();
    /// assert_eq!(not_contained.to_string(), "[1]"); // Not contained
    /// ```
    pub fn array_except(&self, other: RawJsonb) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let left = self.data;
        let right = other.data;

        let left_header = read_u32(left, 0)?;
        let right_header = read_u32(right, 0)?;

        let mut item_map = BTreeMap::new();
        match right_header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                for (jentry, item) in iterate_array(right, right_header) {
                    if let Some(cnt) = item_map.get_mut(&(jentry.clone(), item)) {
                        *cnt += 1;
                    } else {
                        item_map.insert((jentry, item), 1);
                    }
                }
            }
            OBJECT_CONTAINER_TAG => {
                let jentry = JEntry::make_container_jentry(right.len());
                item_map.insert((jentry, right), 1);
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(right, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                item_map.insert((jentry, &right[8..]), 1);
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }

        let mut builder = ArrayBuilder::new(0);
        match left_header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                for (jentry, item) in iterate_array(left, left_header) {
                    if let Some(cnt) = item_map.get_mut(&(jentry.clone(), item)) {
                        if *cnt > 0 {
                            *cnt -= 1;
                            continue;
                        }
                    }
                    builder.push_raw(jentry, item);
                }
            }
            OBJECT_CONTAINER_TAG => {
                let jentry = JEntry::make_container_jentry(left.len());
                if !item_map.contains_key(&(jentry.clone(), left)) {
                    builder.push_raw(jentry, left);
                }
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(left, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                if !item_map.contains_key(&(jentry.clone(), &left[8..])) {
                    builder.push_raw(jentry, &left[8..]);
                }
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }
        builder.build_into(&mut buf);

        Ok(OwnedJsonb::new(buf))
    }

    /// Checks if two JSONB arrays or a JSONB array and an object/scalar have any elements in common.
    ///
    /// This function determines whether two JSONB arrays, or a JSONB array and an object/scalar, share any common elements. The behavior depends on the input types:
    ///
    /// * **Array + Array:** Returns `true` if the two arrays have at least one element in common; otherwise, returns `false`. Duplicate elements are considered; if an element appears multiple times in one array, it only needs to appear at least once in the other array for the function to return `true`.
    /// * **Array + Object/Scalar:** Returns `true` if the array contains the object/scalar; otherwise, returns `false`.
    /// * **Object/Scalar + Array:** Returns `true` if the array contains the object/scalar; otherwise, returns `false`.
    /// * **Object/Scalar + Object/Scalar:** Returns `true` only if both values are exactly equal. This is effectively an equality check.  The values must be completely equal, including any nested structures. For arrays, this would require a recursive equality check for each element in both arrays.
    /// * **Invalid input:** Returns an error if either input is invalid JSONB data.
    ///
    /// # Arguments
    ///
    /// * `self` - The first JSONB value.
    /// * `other` - The second JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the two JSONB values have at least one element in common.
    /// * `Ok(false)` - If the two JSONB values have no elements in common.
    /// * `Err(Error)` - If the input JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Array overlap
    /// let arr1 = r#"[1, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[3, 4, 5]"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(arr1.as_raw().array_overlap(arr2.as_raw()).unwrap()); // True because of '3'
    ///
    /// let arr1 = r#"[1, 2]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[3, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(!arr1.as_raw().array_overlap(arr2.as_raw()).unwrap()); // False, no common elements
    ///
    /// let arr1 = r#"[1, 2, 2]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(arr1.as_raw().array_overlap(arr2.as_raw()).unwrap()); // True, '2' is common
    ///
    /// // Object/scalar overlap (requires complete equality for true)
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(obj1.as_raw().array_overlap(obj2.as_raw()).unwrap()); // True, completely equal
    ///
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(!obj1.as_raw().array_overlap(obj2.as_raw()).unwrap()); // False, not equal
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "1".parse::<OwnedJsonb>().unwrap();
    /// assert!(scalar1.as_raw().array_overlap(scalar2.as_raw()).unwrap()); // True, equal
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "2".parse::<OwnedJsonb>().unwrap();
    /// assert!(!scalar1.as_raw().array_overlap(scalar2.as_raw()).unwrap()); // False, not equal
    ///
    /// // Invalid input
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.array_overlap(arr1.as_raw());
    /// assert!(result.is_err()); // Returns an error
    /// ```
    pub fn array_overlap(&self, other: RawJsonb) -> Result<bool, Error> {
        let left = self.data;
        let right = other.data;

        let left_header = read_u32(left, 0)?;
        let right_header = read_u32(right, 0)?;

        let mut item_set = BTreeSet::new();
        match right_header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                for (jentry, item) in iterate_array(right, right_header) {
                    if !item_set.contains(&(jentry.clone(), item)) {
                        item_set.insert((jentry, item));
                    }
                }
            }
            OBJECT_CONTAINER_TAG => {
                let jentry = JEntry::make_container_jentry(right.len());
                item_set.insert((jentry, right));
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(right, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                item_set.insert((jentry, &right[8..]));
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }

        match left_header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                for (jentry, item) in iterate_array(left, left_header) {
                    if item_set.contains(&(jentry, item)) {
                        return Ok(true);
                    }
                }
            }
            OBJECT_CONTAINER_TAG => {
                let jentry = JEntry::make_container_jentry(left.len());
                if item_set.contains(&(jentry, left)) {
                    return Ok(true);
                }
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(left, 4)?;
                let jentry = JEntry::decode_jentry(encoded);
                if item_set.contains(&(jentry, &left[8..])) {
                    return Ok(true);
                }
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }

        Ok(false)
    }

    /// Inserts or updates a key-value pair in a JSONB object.
    ///
    /// This function inserts a new key-value pair into a JSONB object or updates an existing key-value pair if the key already exists.  The behavior is controlled by the `update_flag`:
    ///
    /// * `update_flag = true`:  If the key already exists, its value is updated with `new_val`. If the key does not exist, it is inserted.
    /// * `update_flag = false`: If the key already exists, an error (`Error::ObjectDuplicateKey`) is returned. If the key does not exist, it is inserted.
    ///
    /// The input JSONB value must be an object; otherwise, an error (`Error::InvalidObject`) is returned.  Invalid JSONB data results in an `Error::InvalidJsonb`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB object.
    /// * `new_key` - The key to insert or update.
    /// * `new_val` - The new value.
    /// * `update_flag` - A boolean indicating whether to update an existing key (true) or fail if a duplicate key is found (false).
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The modified JSONB object.
    /// * `Err(Error)` - If the input is not a JSONB object, if `update_flag` is false and the key already exists, or if the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    ///
    /// // Inserting a new key-value pair
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let new_jsonb = "2".parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.object_insert("b", new_raw_jsonb, false).unwrap();
    /// assert_eq!(inserted.to_string(), r#"{"a":1,"b":2}"#);
    ///
    /// // Updating an existing key-value pair
    /// let updated = inserted.as_raw().object_insert("b", r#"3"#.parse::<OwnedJsonb>().unwrap().as_raw(), true).unwrap();
    /// assert_eq!(updated.to_string(), r#"{"a":1,"b":3}"#);
    ///
    /// // Attempting to insert a duplicate key without update
    /// let result = raw_jsonb.object_insert("a", r#"4"#.parse::<OwnedJsonb>().unwrap().as_raw(), false);
    /// assert!(result.is_err()); // Returns an error because key "a" already exists
    ///
    /// // Invalid JSONB input
    /// let invalid_jsonb = OwnedJsonb::new(vec![1,2,3,4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.object_insert("a", new_raw_jsonb, false);
    /// assert!(result.is_err()); // Returns an error due to invalid JSONB data
    ///
    /// // Inserting into a non-object
    /// let arr_jsonb = "[1,2,3]".parse::<OwnedJsonb>().unwrap();
    /// let arr_raw_jsonb = invalid_jsonb.as_raw();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let result = arr_raw_jsonb.object_insert("a", new_raw_jsonb, false);
    /// assert!(result.is_err()); // Returns an error because input is not a JSONB object
    /// ```
    pub fn object_insert(
        &self,
        new_key: &str,
        new_val: RawJsonb,
        update_flag: bool,
    ) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let value = self.data;
        let new_value = new_val.data;

        let header = read_u32(value, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {}
            ARRAY_CONTAINER_TAG | SCALAR_CONTAINER_TAG => {
                return Err(Error::InvalidObject);
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }

        let mut idx = 0;
        let mut duplicate_key = false;
        for (i, obj_key) in iteate_object_keys(value, header).enumerate() {
            if new_key.eq(obj_key) {
                if !update_flag {
                    return Err(Error::ObjectDuplicateKey);
                }
                idx = i;
                duplicate_key = true;
                break;
            } else if new_key > obj_key {
                idx = i + 1;
            } else {
                break;
            }
        }

        let mut builder = ObjectBuilder::new();
        let mut obj_iter = iterate_object_entries(value, header);
        for _ in 0..idx {
            if let Some((key, jentry, item)) = obj_iter.next() {
                builder.push_raw(key, jentry, item);
            }
        }
        // insert new key and value
        let new_header = read_u32(new_value, 0)?;
        match new_header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG | OBJECT_CONTAINER_TAG => {
                let new_jentry = JEntry::make_container_jentry(new_value.len());
                builder.push_raw(new_key, new_jentry, new_value);
            }
            SCALAR_CONTAINER_TAG => {
                let encoded = read_u32(new_value, 4)?;
                let new_jentry = JEntry::decode_jentry(encoded);
                builder.push_raw(new_key, new_jentry, &new_value[8..]);
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }
        // if the key is duplicated, ignore the original key and value.
        if duplicate_key {
            let _ = obj_iter.next();
        }
        for (key, jentry, item) in obj_iter {
            builder.push_raw(key, jentry, item);
        }
        builder.build_into(&mut buf);

        Ok(OwnedJsonb::new(buf))
    }

    /// Deletes key-value pairs from a JSONB object based on a set of keys.
    ///
    /// This function removes key-value pairs from a JSONB object where the keys are present in the provided `keys` set.  The key comparison is case-sensitive.
    ///
    /// If the input JSONB value is not an object, an error (`Error::InvalidObject`) is returned.  Other invalid JSONB data results in an `Error::InvalidJsonb`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB object.
    /// * `keys` - A set of keys to delete.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The modified JSONB object with the specified keys removed.
    /// * `Err(Error)` - If the input JSONB value is not an object, or if the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use std::collections::BTreeSet;
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": "hello", "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    ///
    /// // Delete keys "a" and "c"
    /// let keys_to_delete: BTreeSet<&str> = ["a", "c"].into_iter().collect();
    /// let deleted = raw_jsonb.object_delete(&keys_to_delete).unwrap();
    /// assert_eq!(deleted.to_string(), r#"{"b":"hello"}"#);
    ///
    /// // Delete a non-existent key
    /// let keys_to_delete: BTreeSet<&str> = ["x"].into_iter().collect();
    /// let deleted = raw_jsonb.object_delete(&keys_to_delete).unwrap();
    /// assert_eq!(deleted.to_string(), r#"{"a":1,"b":"hello","c":3}"#); // Original object returned
    ///
    /// // Attempting to delete from a non-object
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let result = arr_jsonb.as_raw().object_delete(&keys_to_delete);
    /// assert!(result.is_err()); // Returns an error
    ///
    /// // Invalid JSONB data
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.object_delete(&keys_to_delete);
    /// assert!(result.is_err()); // Returns an error
    /// ```
    pub fn object_delete(&self, keys: &BTreeSet<&str>) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let value = self.data;
        let header = read_u32(value, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {}
            ARRAY_CONTAINER_TAG | SCALAR_CONTAINER_TAG => {
                return Err(Error::InvalidObject);
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }

        let mut builder = ObjectBuilder::new();
        for (key, jentry, item) in iterate_object_entries(value, header) {
            if keys.contains(key) {
                continue;
            }
            builder.push_raw(key, jentry, item);
        }
        builder.build_into(&mut buf);

        Ok(OwnedJsonb::new(buf))
    }

    /// Creates a new JSONB object containing only the specified keys from the original object.
    ///
    /// This function selects a subset of key-value pairs from a JSONB object based on the provided `keys` set.  Only key-value pairs where the key is present in the `keys` set are included in the resulting object. The key comparison is case-sensitive.
    ///
    /// If the input JSONB value is not an object, an error (`Error::InvalidObject`) is returned. Invalid JSONB data results in an `Error::InvalidJsonb`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB object.
    /// * `keys` - A set of keys to select.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - A new JSONB object containing only the key-value pairs specified by the `keys` set.  Returns an empty object `{}` if none of the keys are found in the input.
    /// * `Err(Error)` - If the input JSONB value is not an object, or if the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use std::collections::BTreeSet;
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": "hello", "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    ///
    /// // Pick keys "a" and "c"
    /// let keys_to_pick: BTreeSet<&str> = ["a", "c"].into_iter().collect();
    /// let picked = raw_jsonb.object_pick(&keys_to_pick).unwrap();
    /// assert_eq!(picked.to_string(), r#"{"a":1,"c":3}"#);
    ///
    /// // Pick a non-existent key
    /// let keys_to_pick: BTreeSet<&str> = ["x"].into_iter().collect();
    /// let picked = raw_jsonb.object_pick(&keys_to_pick).unwrap();
    /// assert_eq!(picked.to_string(), "{}"); // Empty object returned
    ///
    /// // Attempting to pick from a non-object
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let result = arr_jsonb.as_raw().object_pick(&keys_to_pick);
    /// assert!(result.is_err()); // Returns an error
    ///
    /// // Invalid JSONB data
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.object_pick(&keys_to_pick);
    /// assert!(result.is_err()); // Returns an error
    /// ```
    pub fn object_pick(&self, keys: &BTreeSet<&str>) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let value = self.data;

        let header = read_u32(value, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            OBJECT_CONTAINER_TAG => {}
            ARRAY_CONTAINER_TAG | SCALAR_CONTAINER_TAG => {
                return Err(Error::InvalidObject);
            }
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }

        let mut builder = ObjectBuilder::new();
        for (key, jentry, item) in iterate_object_entries(value, header) {
            if !keys.contains(key) {
                continue;
            }
            builder.push_raw(key, jentry, item);
        }
        builder.build_into(&mut buf);

        Ok(OwnedJsonb::new(buf))
    }

    /// Deletes a value from a JSONB array or object based on a key path.
    ///
    /// This function removes a value from a JSONB array or object using a key path.  The key path is an iterator of `KeyPath` elements specifying the path to the element to delete.
    ///
    /// * **Array:** If the JSONB value is an array, the key path must consist of array indices (`KeyPath::Index`).  A negative index counts from the end of the array (e.g., -1 is the last element).  If the index is out of bounds, the original JSONB value is returned unchanged.
    /// * **Object:** If the JSONB value is an object, the key path can be a mix of object keys (`KeyPath::Name` or `KeyPath::QuotedName`) and array indices.  If any part of the path is invalid (e.g., trying to access an index in a non-array or a key in a non-object), the original JSONB value is returned unchanged.
    /// * **Invalid input:** If the input is neither an array nor an object, or if the JSONB data is otherwise invalid, an error (`Error::InvalidJsonType` or `Error::InvalidJsonb`) is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    /// * `keypath` - An iterator of `KeyPath` elements specifying the path to the element to delete.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The JSONB value with the specified element deleted. Returns the original value if the keypath is invalid or leads to a non-existent value.
    /// * `Err(Error)` - If the input JSONB value is neither an array nor an object, or if the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::keypath::KeyPath;
    /// use jsonb::{OwnedJsonb, RawJsonb};
    /// use std::borrow::Cow;
    ///
    /// // Deleting from an array
    /// let arr_jsonb = r#"[1, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let keypath = [KeyPath::Index(1)]; // Delete element at index 1
    /// let deleted = raw_jsonb.delete_by_keypath(keypath.iter()).unwrap();
    /// assert_eq!(deleted.to_string(), "[1,3]");
    ///
    /// let keypath = [KeyPath::Index(-1)]; // Delete last element
    /// let deleted = raw_jsonb.delete_by_keypath(keypath.iter()).unwrap();
    /// assert_eq!(deleted.to_string(), "[1,2]");
    ///
    /// // Deleting from an object
    /// let obj_jsonb = r#"{"a": {"b": [1, 2, 3]}, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let keypath = [KeyPath::Name(Cow::Borrowed("a")), KeyPath::Name(Cow::Borrowed("b")), KeyPath::Index(1)];
    /// let deleted = raw_jsonb.delete_by_keypath(keypath.iter()).unwrap();
    /// assert_eq!(deleted.to_string(), r#"{"a":{"b":[1,3]},"c":4}"#);
    ///
    /// // Invalid keypath (index out of bounds)
    /// let keypath = [KeyPath::Index(3)];
    /// let deleted = raw_jsonb.delete_by_keypath(keypath.iter()).unwrap();
    /// assert_eq!(deleted.to_string(), r#"{"a":{"b":[1,2,3]},"c":4}"#); // Original value returned
    ///
    /// // Invalid keypath (wrong type)
    /// let keypath = [KeyPath::Name(Cow::Borrowed("a")), KeyPath::Name(Cow::Borrowed("x"))]; // "x" doesn't exist under "a"
    /// let deleted = raw_jsonb.delete_by_keypath(keypath.iter()).unwrap();
    /// assert_eq!(deleted.to_string(), r#"{"a":{"b":[1,2,3]},"c":4}"#); // Original value returned
    ///
    /// // Attempting to delete from a scalar
    /// let scalar_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = scalar_jsonb.as_raw();
    /// let result = raw_jsonb.delete_by_keypath([].iter());
    /// assert!(result.is_err()); // Returns an error
    /// ```
    pub fn delete_by_keypath<'a, I: Iterator<Item = &'a KeyPath<'a>>>(
        &self,
        keypath: I,
    ) -> Result<OwnedJsonb, Error> {
        let mut buf = Vec::new();
        let mut keypath: VecDeque<_> = keypath.collect();
        let value = self.data;
        let header = read_u32(value, 0)?;
        match header & CONTAINER_HEADER_TYPE_MASK {
            ARRAY_CONTAINER_TAG => {
                match self.delete_array_by_keypath(value, header, &mut keypath)? {
                    Some(builder) => {
                        builder.build_into(&mut buf);
                    }
                    None => {
                        buf.extend_from_slice(value);
                    }
                };
            }
            OBJECT_CONTAINER_TAG => {
                match self.delete_object_by_keypath(value, header, &mut keypath)? {
                    Some(builder) => {
                        builder.build_into(&mut buf);
                    }
                    None => {
                        buf.extend_from_slice(value);
                    }
                }
            }
            _ => return Err(Error::InvalidJsonType),
        }
        Ok(OwnedJsonb::new(buf))
    }

    fn delete_array_by_keypath<'a, 'b>(
        &self,
        value: &'b [u8],
        header: u32,
        keypath: &mut VecDeque<&'a KeyPath<'a>>,
    ) -> Result<Option<ArrayBuilder<'b>>, Error> {
        let len = (header & CONTAINER_HEADER_LEN_MASK) as i32;
        match keypath.pop_front() {
            Some(KeyPath::Index(idx)) => {
                let idx = if *idx < 0 { len - idx.abs() } else { *idx };
                if idx < 0 || idx >= len {
                    return Ok(None);
                }
                let mut builder = ArrayBuilder::new(len as usize);
                let idx = idx as usize;
                for (i, entry) in iterate_array(value, header).enumerate() {
                    if i != idx {
                        builder.push_raw(entry.0, entry.1);
                    } else if !keypath.is_empty() {
                        let item_value = entry.1;
                        match entry.0.type_code {
                            CONTAINER_TAG => {
                                let item_header = read_u32(item_value, 0)?;
                                match item_header & CONTAINER_HEADER_TYPE_MASK {
                                    ARRAY_CONTAINER_TAG => {
                                        match self.delete_array_by_keypath(
                                            item_value,
                                            item_header,
                                            keypath,
                                        )? {
                                            Some(item_builder) => builder.push_array(item_builder),
                                            None => return Ok(None),
                                        }
                                    }
                                    OBJECT_CONTAINER_TAG => {
                                        match self.delete_object_by_keypath(
                                            item_value,
                                            item_header,
                                            keypath,
                                        )? {
                                            Some(item_builder) => builder.push_object(item_builder),
                                            None => return Ok(None),
                                        }
                                    }
                                    _ => unreachable!(),
                                }
                            }
                            _ => return Ok(None),
                        }
                    }
                }
                Ok(Some(builder))
            }
            _ => Ok(None),
        }
    }

    fn delete_object_by_keypath<'a, 'b>(
        &self,
        value: &'b [u8],
        header: u32,
        keypath: &mut VecDeque<&'a KeyPath<'a>>,
    ) -> Result<Option<ObjectBuilder<'b>>, Error> {
        match keypath.pop_front() {
            Some(KeyPath::QuotedName(name) | KeyPath::Name(name)) => {
                let mut builder = ObjectBuilder::new();
                for (key, jentry, item) in iterate_object_entries(value, header) {
                    if !key.eq(name) {
                        builder.push_raw(key, jentry, item);
                    } else if !keypath.is_empty() {
                        match jentry.type_code {
                            CONTAINER_TAG => {
                                let item_header = read_u32(item, 0)?;
                                match item_header & CONTAINER_HEADER_TYPE_MASK {
                                    ARRAY_CONTAINER_TAG => {
                                        match self.delete_array_by_keypath(
                                            item,
                                            item_header,
                                            keypath,
                                        )? {
                                            Some(item_builder) => {
                                                builder.push_array(key, item_builder)
                                            }
                                            None => return Ok(None),
                                        }
                                    }
                                    OBJECT_CONTAINER_TAG => {
                                        match self.delete_object_by_keypath(
                                            item,
                                            item_header,
                                            keypath,
                                        )? {
                                            Some(item_builder) => {
                                                builder.push_object(key, item_builder)
                                            }
                                            None => return Ok(None),
                                        }
                                    }
                                    _ => unreachable!(),
                                }
                            }
                            _ => return Ok(None),
                        }
                    }
                }
                Ok(Some(builder))
            }
            _ => Ok(None),
        }
    }

    /// Convert `JSONB` value to comparable vector.
    /// The compare rules are the same as the `compare` function.
    /// Scalar Null > Array > Object > Other Scalars(String > Number > Boolean).
    pub fn convert_to_comparable(&self) -> Vec<u8> {
        let value = self.data;
        let mut buf = Vec::new();
        let depth = 0;
        let header = read_u32(value, 0).unwrap_or_default();
        match header & CONTAINER_HEADER_TYPE_MASK {
            SCALAR_CONTAINER_TAG => {
                let encoded = match read_u32(value, 4) {
                    Ok(encoded) => encoded,
                    Err(_) => {
                        return buf;
                    }
                };
                let jentry = JEntry::decode_jentry(encoded);
                Self::scalar_convert_to_comparable(depth, &jentry, &value[8..], &mut buf);
            }
            ARRAY_CONTAINER_TAG => {
                buf.push(depth);
                buf.push(ARRAY_LEVEL);
                let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
                Self::array_convert_to_comparable(depth + 1, length, &value[4..], &mut buf);
            }
            OBJECT_CONTAINER_TAG => {
                buf.push(depth);
                buf.push(OBJECT_LEVEL);
                let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
                Self::object_convert_to_comparable(depth + 1, length, &value[4..], &mut buf);
            }
            _ => {}
        }
        buf
    }

    fn scalar_convert_to_comparable(depth: u8, jentry: &JEntry, value: &[u8], buf: &mut Vec<u8>) {
        buf.push(depth);
        let level = jentry_compare_level(jentry);
        match jentry.type_code {
            CONTAINER_TAG => {
                let header = match read_u32(value, 0) {
                    Ok(header) => header,
                    Err(_) => {
                        return;
                    }
                };
                let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
                match header & CONTAINER_HEADER_TYPE_MASK {
                    ARRAY_CONTAINER_TAG => {
                        buf.push(ARRAY_LEVEL);
                        Self::array_convert_to_comparable(depth + 1, length, &value[4..], buf);
                    }
                    OBJECT_CONTAINER_TAG => {
                        buf.push(OBJECT_LEVEL);
                        Self::object_convert_to_comparable(depth + 1, length, &value[4..], buf);
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
                        if let Ok(num) = Number::decode(&value[..length]) {
                            let n = num.as_f64().unwrap();
                            // https://github.com/rust-lang/rust/blob/9c20b2a8cc7588decb6de25ac6a7912dcef24d65/library/core/src/num/f32.rs#L1176-L1260
                            let s = n.to_bits() as i64;
                            let v = s ^ (((s >> 63) as u64) >> 1) as i64;
                            let mut b = v.to_be_bytes();
                            // Toggle top "sign" bit to ensure consistent sort order
                            b[0] ^= 0x80;
                            buf.extend_from_slice(&b);
                        }
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
            let encoded = match read_u32(value, jentry_offset) {
                Ok(encoded) => encoded,
                Err(_) => {
                    return;
                }
            };
            let jentry = JEntry::decode_jentry(encoded);
            Self::scalar_convert_to_comparable(depth, &jentry, &value[val_offset..], buf);
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
            let encoded = match read_u32(value, jentry_offset) {
                Ok(encoded) => encoded,
                Err(_) => {
                    return;
                }
            };
            let key_jentry = JEntry::decode_jentry(encoded);

            jentry_offset += 4;
            val_offset += key_jentry.length as usize;
            key_jentries.push_back(key_jentry);
        }

        let mut key_offset = 8 * length;
        for _ in 0..length {
            let key_jentry = key_jentries.pop_front().unwrap();
            Self::scalar_convert_to_comparable(depth, &key_jentry, &value[key_offset..], buf);

            let encoded = match read_u32(value, jentry_offset) {
                Ok(encoded) => encoded,
                Err(_) => {
                    return;
                }
            };
            let val_jentry = JEntry::decode_jentry(encoded);
            Self::scalar_convert_to_comparable(depth, &val_jentry, &value[val_offset..], buf);

            jentry_offset += 4;
            key_offset += key_jentry.length as usize;
            val_offset += val_jentry.length as usize;
        }
    }
}

fn get_jentry_by_name(
    value: &[u8],
    offset: usize,
    header: u32,
    name: &str,
    ignore_case: bool,
) -> Option<(JEntry, u32, usize)> {
    let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
    let mut jentry_offset = offset + 4;
    let mut val_offset = offset + 8 * length + 4;

    let mut key_jentries: VecDeque<JEntry> = VecDeque::with_capacity(length);
    for _ in 0..length {
        let encoded = read_u32(value, jentry_offset).ok()?;
        let key_jentry = JEntry::decode_jentry(encoded);

        jentry_offset += 4;
        val_offset += key_jentry.length as usize;
        key_jentries.push_back(key_jentry);
    }

    let mut result = None;
    let mut key_offset = offset + 8 * length + 4;

    while let Some(key_jentry) = key_jentries.pop_front() {
        let prev_key_offset = key_offset;
        key_offset += key_jentry.length as usize;
        let key = unsafe { std::str::from_utf8_unchecked(&value[prev_key_offset..key_offset]) };

        let val_encoded = read_u32(value, jentry_offset).ok()?;
        let val_jentry = JEntry::decode_jentry(val_encoded);
        let val_length = val_jentry.length as usize;

        // first match the value with the same name, if not found,
        // then match the value with the ignoring case name.
        if name.eq(key) {
            result = Some((val_jentry, val_encoded, val_offset));
            break;
        } else if ignore_case && name.eq_ignore_ascii_case(key) && result.is_none() {
            result = Some((val_jentry, val_encoded, val_offset));
        }

        jentry_offset += 4;
        val_offset += val_length;
    }
    result
}

fn get_jentry_by_index(
    value: &[u8],
    offset: usize,
    header: u32,
    index: usize,
) -> Option<(JEntry, u32, usize)> {
    let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
    if index >= length {
        return None;
    }
    let mut jentry_offset = offset + 4;
    let mut val_offset = offset + 4 * length + 4;

    for i in 0..length {
        let encoded = read_u32(value, jentry_offset).ok()?;
        let jentry = JEntry::decode_jentry(encoded);
        let val_length = jentry.length as usize;
        if i < index {
            jentry_offset += 4;
            val_offset += val_length;
            continue;
        }
        return Some((jentry, encoded, val_offset));
    }
    None
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

fn extract_by_jentry(jentry: &JEntry, encoded: u32, offset: usize, value: &[u8]) -> Vec<u8> {
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

fn read_u32(buf: &[u8], idx: usize) -> Result<u32, Error> {
    let bytes: [u8; 4] = buf
        .get(idx..idx + 4)
        .ok_or(Error::InvalidEOF)?
        .try_into()
        .unwrap();
    Ok(u32::from_be_bytes(bytes))
}
