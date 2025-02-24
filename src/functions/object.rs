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

use crate::raw::JsonbItem;
use crate::ValueType;
use std::collections::BTreeSet;
use std::str::from_utf8;

use crate::core::ArrayBuilder;
use crate::core::ArrayIterator;
use crate::core::ObjectBuilder;
use crate::core::ObjectIterator;
use crate::core::ObjectKeyIterator;
use crate::core::OwnedObjectBuilder;

use crate::error::*;

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
    ) -> Result<OwnedJsonb> {
        let mut builder = OwnedObjectBuilder::new();
        for (key, val_jsonb) in items.into_iter() {
            let key_str = key.as_ref().to_string();
            builder.push_owned_jsonb(key_str, val_jsonb.to_owned())?;
        }
        builder.build()
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
    /// use jsonb::OwnedJsonb;
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
    pub fn object_keys(&self) -> Result<Option<OwnedJsonb>> {
        let object_key_iter_opt = ObjectKeyIterator::new(*self)?;
        match object_key_iter_opt {
            Some(mut object_key_iter) => {
                let mut builder = ArrayBuilder::with_capacity(object_key_iter.len());
                for key_result in &mut object_key_iter {
                    let key_item = key_result?;
                    builder.push_raw_jsonb_item(key_item);
                }
                Ok(Some(builder.build()?))
            }
            None => Ok(None),
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
    /// use jsonb::OwnedJsonb;
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
    pub fn object_each(&self) -> Result<Option<Vec<(String, OwnedJsonb)>>> {
        let object_iter_opt = ObjectIterator::new(*self)?;
        match object_iter_opt {
            Some(mut object_iter) => {
                let mut items = Vec::with_capacity(object_iter.len());
                for result in &mut object_iter {
                    let (key, val_item) = result?;
                    let owned_jsonb_val = OwnedJsonb::from_item(val_item)?;
                    items.push((key.to_string(), owned_jsonb_val));
                }
                Ok(Some(items))
            }
            None => Ok(None),
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
    /// use jsonb::OwnedJsonb;
    ///
    /// // Inserting a new key-value pair
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let new_jsonb = "2".parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.object_insert("b", &new_raw_jsonb, false).unwrap();
    /// assert_eq!(inserted.to_string(), r#"{"a":1,"b":2}"#);
    ///
    /// // Updating an existing key-value pair
    /// let new_jsonb = r#"3"#.parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let updated = inserted.as_raw().object_insert("b", &new_raw_jsonb, true).unwrap();
    /// assert_eq!(updated.to_string(), r#"{"a":1,"b":3}"#);
    ///
    /// // Attempting to insert a duplicate key without update
    /// let result = raw_jsonb.object_insert("a", &new_raw_jsonb, false);
    /// assert!(result.is_err()); // Returns an error because key "a" already exists
    ///
    /// // Invalid JSONB input
    /// let invalid_jsonb = OwnedJsonb::new(vec![1,2,3,4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.object_insert("a", &new_raw_jsonb, false);
    /// assert!(result.is_err()); // Returns an error due to invalid JSONB data
    ///
    /// // Inserting into a non-object
    /// let arr_jsonb = "[1,2,3]".parse::<OwnedJsonb>().unwrap();
    /// let arr_raw_jsonb = invalid_jsonb.as_raw();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let result = arr_raw_jsonb.object_insert("a", &new_raw_jsonb, false);
    /// assert!(result.is_err()); // Returns an error because input is not a JSONB object
    /// ```
    pub fn object_insert(
        &self,
        new_key: &str,
        new_val: &RawJsonb,
        update_flag: bool,
    ) -> Result<OwnedJsonb> {
        let mut builder = ObjectBuilder::new();
        let object_iter_opt = ObjectIterator::new(*self)?;
        match object_iter_opt {
            Some(mut object_iter) => {
                for result in &mut object_iter {
                    let (key, val_item) = result?;
                    if new_key.eq(key) {
                        if !update_flag {
                            return Err(Error::ObjectDuplicateKey);
                        }
                    } else {
                        builder.push_raw_jsonb_item(key, val_item)?;
                    }
                }
                let new_val_item = JsonbItem::from_raw_jsonb(*new_val)?;
                builder.push_raw_jsonb_item(new_key, new_val_item)?;
            }
            None => {
                return Err(Error::InvalidObject);
            }
        }
        builder.build()
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
    /// use jsonb::OwnedJsonb;
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
    pub fn object_delete(&self, keys: &BTreeSet<&str>) -> Result<OwnedJsonb> {
        let mut builder = ObjectBuilder::new();
        let object_iter_opt = ObjectIterator::new(*self)?;
        match object_iter_opt {
            Some(mut object_iter) => {
                for result in &mut object_iter {
                    let (key, val_item) = result?;
                    if keys.contains(key) {
                        continue;
                    }
                    builder.push_raw_jsonb_item(key, val_item)?;
                }
            }
            None => {
                return Err(Error::InvalidObject);
            }
        }
        builder.build()
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
    /// use jsonb::OwnedJsonb;
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
    pub fn object_pick(&self, keys: &BTreeSet<&str>) -> Result<OwnedJsonb> {
        let mut builder = ObjectBuilder::new();
        let object_iter_opt = ObjectIterator::new(*self)?;
        match object_iter_opt {
            Some(mut object_iter) => {
                for result in &mut object_iter {
                    let (key, val_item) = result?;
                    if !keys.contains(key) {
                        continue;
                    }
                    builder.push_raw_jsonb_item(key, val_item)?;
                }
            }
            None => {
                return Err(Error::InvalidObject);
            }
        }
        builder.build()
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
    /// use jsonb::OwnedJsonb;
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
    pub fn exists_all_keys<'a, I: Iterator<Item = &'a [u8]>>(&self, keys: I) -> Result<bool> {
        let mut self_keys = BTreeSet::new();
        let value_type = self.value_type()?;
        match value_type {
            ValueType::Object(_) => {
                let mut object_key_iter = ObjectKeyIterator::new(*self)?.unwrap();
                for result in &mut object_key_iter {
                    let item = result?;
                    if let Some(obj_key) = item.as_str() {
                        self_keys.insert(obj_key);
                    }
                }
            }
            ValueType::Array(_) => {
                let mut array_iter = ArrayIterator::new(*self)?.unwrap();
                for result in &mut array_iter {
                    let item = result?;
                    if let Some(arr_key) = item.as_str() {
                        self_keys.insert(arr_key);
                    }
                }
            }
            _ => {}
        }
        for key in keys {
            if let Ok(key) = from_utf8(key) {
                if !self_keys.contains(key) {
                    return Ok(false);
                }
            } else {
                return Ok(false);
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
    /// use jsonb::OwnedJsonb;
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
    pub fn exists_any_keys<'a, I: Iterator<Item = &'a [u8]>>(&self, keys: I) -> Result<bool> {
        let mut self_keys = BTreeSet::new();
        let value_type = self.value_type()?;
        match value_type {
            ValueType::Object(_) => {
                let mut object_key_iter = ObjectKeyIterator::new(*self)?.unwrap();
                for result in &mut object_key_iter {
                    let item = result?;
                    if let Some(obj_key) = item.as_str() {
                        self_keys.insert(obj_key);
                    }
                }
            }
            ValueType::Array(_) => {
                let mut array_iter = ArrayIterator::new(*self)?.unwrap();
                for result in &mut array_iter {
                    let item = result?;
                    if let Some(arr_key) = item.as_str() {
                        self_keys.insert(arr_key);
                    }
                }
            }
            _ => {}
        }
        if !self_keys.is_empty() {
            for key in keys {
                if let Ok(key) = from_utf8(key) {
                    if self_keys.contains(key) {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }
}
