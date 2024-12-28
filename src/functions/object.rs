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

// This file contains functions that specifically operate on JSONB object values.

use core::convert::TryInto;
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::str::from_utf8;
use std::str::from_utf8_unchecked;

use crate::builder::ObjectBuilder;
use crate::constants::*;
use crate::error::*;
use crate::functions::core::extract_by_jentry;
use crate::functions::core::read_u32;
use crate::iterator::iteate_object_keys;
use crate::iterator::iterate_array;
use crate::iterator::iterate_object_entries;
use crate::jentry::JEntry;

use crate::OwnedJsonb;
use crate::RawJsonb;

impl OwnedJsonb {
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
}
