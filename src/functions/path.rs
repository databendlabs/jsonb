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

// This file contains functions that dealing with path-based access to JSONB data.

use std::collections::VecDeque;
use std::str::from_utf8_unchecked;

use crate::builder::ArrayBuilder;
use crate::builder::ObjectBuilder;
use crate::constants::*;
use crate::error::*;
use crate::functions::core::extract_by_jentry;
use crate::functions::core::read_u32;
use crate::iterator::iterate_array;
use crate::iterator::iterate_object_entries;
use crate::jentry::JEntry;
use crate::jsonpath::JsonPath;
use crate::jsonpath::Mode;
use crate::jsonpath::Selector;
use crate::keypath::KeyPath;

use crate::OwnedJsonb;
use crate::RawJsonb;

impl RawJsonb<'_> {
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
                    match get_jentry_by_name(value, curr_val_offset, header, &name, false) {
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
}

pub(crate) fn get_jentry_by_name(
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

pub(crate) fn get_jentry_by_index(
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
