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

// This file contains functions that don't neatly fit into other categories.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::VecDeque;

use crate::constants::*;
use crate::core::compare_entries;
use crate::core::ArrayBuilder;
use crate::core::ArrayIterator;
use crate::core::Entries;
use crate::core::JsonbItem;
use crate::core::JsonbItemType;
use crate::core::ObjectBuilder;
use crate::core::ObjectIterator;
use crate::core::OrderedEntry;
use crate::core::RawEntry;
use crate::error::*;
use crate::number::Number;
use crate::ExtensionValue;
use crate::OwnedJsonb;
use crate::RawJsonb;

impl RawJsonb<'_> {
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
    /// * `"decimal"`
    /// * `"binary"`
    /// * `"date"`
    /// * `"timestamp"`
    /// * `"timestamp_tz"`
    /// * `"interval"`
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///    
    /// # Returns
    ///
    /// * `Ok(&'static str)` - A string slice representing the type of the JSONB value.
    /// * `Err(Error)` - If an error occurred during decoding (e.g., invalid JSONB data).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
    ///
    /// // Type checking
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "ARRAY");
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "OBJECT");
    ///
    /// let num_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = num_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "INTEGER");
    ///
    /// let string_jsonb = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = string_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "STRING");
    ///
    /// let bool_jsonb = "true".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = bool_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "BOOLEAN");
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = null_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.type_of().unwrap(), "NULL_VALUE");
    /// ```
    pub fn type_of(&self) -> Result<&'static str> {
        let jsonb_item_type = self.jsonb_item_type()?;
        match jsonb_item_type {
            JsonbItemType::Null => Ok(TYPE_NULL),
            JsonbItemType::Boolean => Ok(TYPE_BOOLEAN),
            JsonbItemType::Number => {
                let jsonb_item = JsonbItem::from_raw_jsonb(*self)?;
                match jsonb_item {
                    JsonbItem::Number(num) => {
                        let val = num.as_number()?;
                        match val {
                            Number::UInt64(_) | Number::Int64(_) => Ok(TYPE_INTEGER),
                            Number::Decimal64(_)
                            | Number::Decimal128(_)
                            | Number::Decimal256(_) => Ok(TYPE_DECIMAL),
                            Number::Float64(_) => Ok(TYPE_DOUBLE),
                        }
                    }
                    _ => Err(Error::InvalidJsonb),
                }
            }
            JsonbItemType::String => Ok(TYPE_STRING),
            JsonbItemType::Extension => {
                let jsonb_item = JsonbItem::from_raw_jsonb(*self)?;
                match jsonb_item {
                    JsonbItem::Extension(ext) => {
                        let val = ext.as_extension_value()?;
                        match val {
                            ExtensionValue::Binary(_v) => Ok(TYPE_BINARY),
                            ExtensionValue::Date(_v) => Ok(TYPE_DATE),
                            ExtensionValue::Timestamp(_v) => Ok(TYPE_TIMESTAMP),
                            ExtensionValue::TimestampTz(_v) => Ok(TYPE_TIMESTAMP_TZ),
                            ExtensionValue::Interval(_v) => Ok(TYPE_INTERVAL),
                        }
                    }
                    _ => Err(Error::InvalidJsonb),
                }
            }
            JsonbItemType::Array(_) => Ok(TYPE_ARRAY),
            JsonbItemType::Object(_) => Ok(TYPE_OBJECT),
        }
    }

    /// Checks if the JSONB value contains other JSONB value.
    ///
    /// Containment is defined as follows:
    ///
    /// * **Scalar values:** Two scalar values are considered equal if their byte representations are identical.
    /// * **Objects:** The self object contains the other object if all key-value pairs in the other object
    ///   exist in the self object with the same values. The self object may have additional key-value pairs.
    /// * **Arrays:** The self array contains the other array if, for every element in the other array, there exists
    ///   an identical element in the self array. The self array may have additional elements. Note that order does
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
    /// use jsonb::OwnedJsonb;
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
    pub fn contains(&self, other: &RawJsonb) -> Result<bool> {
        self.contains_with_depth(other, 0)
    }

    /// Implements [`RawJsonb::contains`], where `depth` is the number of enclosing containers.
    fn contains_with_depth(&self, other: &RawJsonb, depth: usize) -> Result<bool> {
        let self_type = self.jsonb_item_type()?;
        let other_type = other.jsonb_item_type()?;
        match (self_type, other_type) {
            (JsonbItemType::Object(self_len), JsonbItemType::Object(other_len)) => {
                let depth = enter_container(depth)?;
                if self_len < other_len {
                    return Ok(false);
                }
                let (keys, values) = Entries::object(*self, self_len)?;
                let mut self_map = BTreeMap::new();
                for (key, value) in keys.zip(values) {
                    self_map.insert(key?.payload, value?);
                }
                let (keys, values) = Entries::object(*other, other_len)?;
                for (key, other_value) in keys.zip(values) {
                    let (key, other_value) = (key?, other_value?);
                    let Some(self_value) = self_map.get(key.payload) else {
                        return Ok(false);
                    };
                    let contained = if self_value.is_container() && other_value.is_container() {
                        let other_container = other_value.container();
                        self_value
                            .container()
                            .contains_with_depth(&other_container, depth)?
                    } else {
                        compare_entries(*self_value, other_value, depth) == Some(Ordering::Equal)
                    };
                    if !contained {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (JsonbItemType::Array(self_len), JsonbItemType::Array(other_len)) => {
                let depth = enter_container(depth)?;
                let mut self_scalar_set = BTreeSet::new();
                let mut self_container_set = BTreeSet::new();
                for item in Entries::new(*self, self_len) {
                    let item = item?;
                    if item.is_container() {
                        self_container_set.insert(item.container());
                    } else {
                        self_scalar_set.insert(OrderedEntry(item));
                    }
                }
                for item in Entries::new(*other, other_len) {
                    let item = item?;
                    if item.is_container() {
                        let other_sub_item = item.container();
                        let mut contains = false;
                        for self_sub_item in self_container_set.iter() {
                            if self_sub_item.contains_with_depth(&other_sub_item, depth)? {
                                contains = true;
                                break;
                            }
                        }
                        if !contains {
                            return Ok(false);
                        }
                    } else if !self_scalar_set.contains(&OrderedEntry(item)) {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (
                JsonbItemType::Array(self_len),
                JsonbItemType::Null
                | JsonbItemType::Boolean
                | JsonbItemType::Number
                | JsonbItemType::String,
            ) => {
                let mut self_item_set = BTreeSet::new();
                for item in Entries::new(*self, self_len) {
                    let item = item?;
                    // other value is scalar, ignore container items.
                    if !item.is_container() {
                        self_item_set.insert(OrderedEntry(item));
                    }
                }
                let other_item = OrderedEntry(RawEntry::from_jsonb(*other)?);
                Ok(self_item_set.contains(&other_item))
            }
            (
                JsonbItemType::Null
                | JsonbItemType::Boolean
                | JsonbItemType::Number
                | JsonbItemType::String,
                JsonbItemType::Null
                | JsonbItemType::Boolean
                | JsonbItemType::Number
                | JsonbItemType::String,
            ) => Ok(self.eq(other)),
            (_, _) => Ok(false),
        }
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
    /// use jsonb::OwnedJsonb;
    ///
    /// let jsonb_value = r#"{"a": "hello", "b": [1, "world", {"c": "rust"}]}"#
    ///     .parse::<OwnedJsonb>()
    ///     .unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    ///
    /// // Check if any string contains "rust"
    /// let contains_rust = raw_jsonb
    ///     .traverse_check_string(|s| s.eq("rust".as_bytes()))
    ///     .unwrap();
    /// assert!(contains_rust);
    ///
    /// // Check if any string contains "xyz"
    /// let contains_xyz = raw_jsonb
    ///     .traverse_check_string(|s| s.eq("xyz".as_bytes()))
    ///     .unwrap();
    /// assert!(!contains_xyz);
    ///
    /// // Check if any string is longer than 5 characters
    /// let long_string = raw_jsonb.traverse_check_string(|s| s.len() > 5).unwrap();
    /// assert!(!long_string);
    ///
    /// // Example with an array of strings
    /// let jsonb_value = r#"["hello", "world", "rust"]"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let contains_rust = raw_jsonb
    ///     .traverse_check_string(|s| s.eq("rust".as_bytes()))
    ///     .unwrap();
    /// assert!(contains_rust);
    /// ```
    pub fn traverse_check_string(&self, func: impl Fn(&[u8]) -> bool) -> Result<bool> {
        let mut raw_jsonbs = VecDeque::new();
        raw_jsonbs.push_back(*self);
        while let Some(raw_jsonb) = raw_jsonbs.pop_front() {
            let jsonb_item_type = raw_jsonb.jsonb_item_type()?;
            match jsonb_item_type {
                JsonbItemType::Array(_) => {
                    let mut array_iter = ArrayIterator::new(raw_jsonb)?.unwrap();
                    for item_result in &mut array_iter {
                        let item = item_result?;
                        if let Some(s) = item.as_str() {
                            if func(s.as_bytes()) {
                                return Ok(true);
                            }
                        } else if let Some(inner_raw_jsonb) = item.as_raw_jsonb() {
                            raw_jsonbs.push_back(inner_raw_jsonb);
                        }
                    }
                }
                JsonbItemType::Object(_) => {
                    let mut object_iter = ObjectIterator::new(raw_jsonb)?.unwrap();
                    for result in &mut object_iter {
                        let (key, val_item) = result?;
                        if func(key.as_bytes()) {
                            return Ok(true);
                        }
                        if let Some(s) = val_item.as_str() {
                            if func(s.as_bytes()) {
                                return Ok(true);
                            }
                        } else if let Some(inner_raw_jsonb) = val_item.as_raw_jsonb() {
                            raw_jsonbs.push_back(inner_raw_jsonb);
                        }
                    }
                }
                _ => {
                    if let Some(s) = raw_jsonb.as_str()? {
                        if func(s.as_bytes()) {
                            return Ok(true);
                        }
                    }
                }
            }
        }
        Ok(false)
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
    /// * **Object/Scalar + Object/Scalar:** Creates a new array containing the `self` and `other` (as a single element).
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
    /// use jsonb::OwnedJsonb;
    ///
    /// // Object + Object
    /// let obj1 = r#"{"a": 1, "b": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"b": 3, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let concatenated = obj1.as_raw().concat(&obj2.as_raw()).unwrap();
    /// assert_eq!(concatenated.to_string(), r#"{"a":1,"b":3,"c":4}"#); // "b" is overwritten
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
    pub fn concat(&self, other: &RawJsonb) -> Result<OwnedJsonb> {
        let self_type = self.jsonb_item_type()?;
        let other_type = other.jsonb_item_type()?;
        match (self_type, other_type) {
            (JsonbItemType::Object(_), JsonbItemType::Object(_)) => {
                let mut self_object_iter = ObjectIterator::new(*self)?.unwrap();
                let mut other_object_iter = ObjectIterator::new(*other)?.unwrap();
                let mut builder = ObjectBuilder::new();
                for result in &mut other_object_iter {
                    let (key, val_item) = result?;
                    builder.push_jsonb_item(key, val_item)?;
                }
                for result in &mut self_object_iter {
                    let (key, val_item) = result?;
                    // if key duplicate, keep value from other object
                    if !builder.contains_key(key) {
                        builder.push_jsonb_item(key, val_item)?;
                    }
                }
                Ok(builder.build()?)
            }
            (JsonbItemType::Array(_), JsonbItemType::Array(_)) => {
                let mut self_array_iter = ArrayIterator::new(*self)?.unwrap();
                let mut other_array_iter = ArrayIterator::new(*other)?.unwrap();
                let len = self_array_iter.len() + other_array_iter.len();
                let mut builder = ArrayBuilder::with_capacity(len);
                for item_result in &mut self_array_iter {
                    let item = item_result?;
                    builder.push_jsonb_item(item);
                }
                for item_result in &mut other_array_iter {
                    let item = item_result?;
                    builder.push_jsonb_item(item);
                }
                Ok(builder.build()?)
            }
            (_, JsonbItemType::Array(_)) => {
                let mut other_array_iter = ArrayIterator::new(*other)?.unwrap();
                let len = other_array_iter.len() + 1;
                let mut builder = ArrayBuilder::with_capacity(len);
                builder.push_raw_jsonb(*self);
                for item_result in &mut other_array_iter {
                    let item = item_result?;
                    builder.push_jsonb_item(item);
                }
                Ok(builder.build()?)
            }
            (JsonbItemType::Array(_), _) => {
                let mut self_array_iter = ArrayIterator::new(*self)?.unwrap();
                let len = self_array_iter.len() + 1;
                let mut builder = ArrayBuilder::with_capacity(len);
                for item_result in &mut self_array_iter {
                    let item = item_result?;
                    builder.push_jsonb_item(item);
                }
                builder.push_raw_jsonb(*other);
                Ok(builder.build()?)
            }
            (_, _) => {
                let mut builder = ArrayBuilder::with_capacity(2);
                builder.push_raw_jsonb(*self);
                builder.push_raw_jsonb(*other);
                Ok(builder.build()?)
            }
        }
    }

    /// Recursively reomves all object key-value pairs that have null values from a JSONB object.
    ///
    /// Note: null values in the JSONB array are not reomved.
    ///
    /// # Arguments
    ///
    /// * `self` - The first JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The JSONB value with nulls removed.
    /// * `Err(Error)` - If the input JSONB value is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn strip_nulls(&self) -> Result<OwnedJsonb> {
        self.strip_nulls_with_depth(0)
    }

    /// Implements [`RawJsonb::strip_nulls`], where `depth` is the number of enclosing containers.
    fn strip_nulls_with_depth(&self, depth: usize) -> Result<OwnedJsonb> {
        let jsonb_item_type = self.jsonb_item_type()?;
        match jsonb_item_type {
            JsonbItemType::Array(_) => {
                let depth = enter_container(depth)?;
                let mut array_iter = ArrayIterator::new(*self)?.unwrap();
                let mut builder = ArrayBuilder::with_capacity(array_iter.len());
                for item_result in &mut array_iter {
                    let item = item_result?;
                    if let Some(sub_item) = item.as_raw_jsonb() {
                        let no_nulls_item = sub_item.strip_nulls_with_depth(depth)?;
                        builder.push_owned_jsonb(no_nulls_item);
                    } else {
                        builder.push_jsonb_item(item);
                    }
                }
                Ok(builder.build()?)
            }
            JsonbItemType::Object(_) => {
                let depth = enter_container(depth)?;
                let mut object_iter = ObjectIterator::new(*self)?.unwrap();
                let mut builder = ObjectBuilder::new();
                for result in &mut object_iter {
                    let (key, val_item) = result?;
                    if val_item.as_null().is_some() {
                        continue;
                    } else if let Some(sub_item) = val_item.as_raw_jsonb() {
                        let no_nulls_item = sub_item.strip_nulls_with_depth(depth)?;
                        builder.push_owned_jsonb(key, no_nulls_item)?;
                    } else {
                        builder.push_jsonb_item(key, val_item)?;
                    }
                }
                Ok(builder.build()?)
            }
            _ => Ok(self.to_owned()),
        }
    }

    /// Converts a RawJsonb value into a comparable binary representation.
    ///
    /// This function transforms the JSONB value into a new binary format designed for efficient comparison.
    /// The resulting binary data can be directly compared using byte-wise operations to determine the relative order of two JSONB values.
    /// The original JSONB data structure is flattened into a linear representation, and different data types are encoded in a way that enables direct comparison.
    /// The compare rules are the same as the `PartialOrd` trait.
    /// Scalar Null > Array > Object > Other Scalars(String > Number > Boolean).
    ///
    /// **Important:** The resulting byte array is *not* a valid JSONB format;
    /// it's specifically designed for comparison purposes and should not be interpreted as standard JSONB data.
    /// The encoding may change between versions, so it is meant for in-memory
    /// sorting and must not be persisted.
    ///
    /// Each value is prefixed with its nesting depth as a big-endian `u16`,
    /// followed by a type level byte.
    ///
    /// # Arguments
    ///
    /// * `self` - The RawJsonb value to convert.
    ///
    /// # Returns
    ///
    /// A `Vec<u8>` representing the comparable binary form of the JSONB data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
    ///
    /// let json1 = r#"{"a":1,"b":"hello"}"#.parse::<OwnedJsonb>().unwrap();
    /// let json2 = r#"{"a":1,"b":"world"}"#.parse::<OwnedJsonb>().unwrap();
    /// let json3 = r#"{"a":2,"b":"hello"}"#.parse::<OwnedJsonb>().unwrap();
    /// let json4 = r#"{"a":1,"b":[1,2,3]}"#.parse::<OwnedJsonb>().unwrap();
    /// let json5 = r#"{"a":1,"b":[1,2]}"#.parse::<OwnedJsonb>().unwrap();
    /// let json6 = "[1,2,3]".parse::<OwnedJsonb>().unwrap();
    /// let json7 = "[1,2]".parse::<OwnedJsonb>().unwrap();
    /// let json8 = "1".parse::<OwnedJsonb>().unwrap();
    /// let json9 = "2".parse::<OwnedJsonb>().unwrap();
    ///
    /// let comparable1 = json1.as_raw().convert_to_comparable();
    /// let comparable2 = json2.as_raw().convert_to_comparable();
    /// let comparable3 = json3.as_raw().convert_to_comparable();
    /// let comparable4 = json4.as_raw().convert_to_comparable();
    /// let comparable5 = json5.as_raw().convert_to_comparable();
    /// let comparable6 = json6.as_raw().convert_to_comparable();
    /// let comparable7 = json7.as_raw().convert_to_comparable();
    /// let comparable8 = json8.as_raw().convert_to_comparable();
    /// let comparable9 = json9.as_raw().convert_to_comparable();
    ///
    /// assert!(comparable1 < comparable2);
    /// assert!(comparable1 < comparable3);
    /// assert!(comparable1 < comparable4);
    /// assert!(comparable4 > comparable5);
    /// assert!(comparable6 > comparable7);
    /// assert!(comparable8 < comparable9);
    /// ```
    pub fn convert_to_comparable(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.len());
        match RawEntry::from_jsonb(*self).and_then(|entry| entry.write_comparable(0, &mut buf)) {
            Ok(()) => buf,
            Err(_) => vec![],
        }
    }
}

/// Appends the depth and type level that prefix every value in the comparable encoding.
///
/// The depth is written as a big-endian `u16` so that byte-wise comparison
/// orders depths numerically: a smaller depth at the same position means the
/// enclosing container has ended, which makes the shorter container sort first.
///
/// # Errors
///
/// Returns `Error::RecursionLimitExceeded` if `depth` does not fit in a `u16`,
/// which [`MAX_NESTING_DEPTH`] already rules out.
fn push_comparable_tag(buf: &mut Vec<u8>, depth: usize, level: u8) -> Result<()> {
    let depth = u16::try_from(depth).map_err(|_| Error::RecursionLimitExceeded)?;
    buf.extend_from_slice(&depth.to_be_bytes());
    buf.push(level);
    Ok(())
}

impl RawEntry<'_> {
    /// Appends the comparable encoding of this entry to `buf`; see
    /// [`RawJsonb::convert_to_comparable`]. `depth` is the number of
    /// containers enclosing this entry.
    fn write_comparable(self, depth: usize, buf: &mut Vec<u8>) -> Result<()> {
        let entry = self.unwrap_scalar()?;
        match entry.item_type()? {
            JsonbItemType::Array(len) => {
                let child_depth = enter_container(depth)?;
                push_comparable_tag(buf, depth, ARRAY_LEVEL)?;
                for item in Entries::new(entry.container(), len) {
                    item?.write_comparable(child_depth, buf)?;
                }
            }
            JsonbItemType::Object(len) => {
                let child_depth = enter_container(depth)?;
                push_comparable_tag(buf, depth, OBJECT_LEVEL)?;
                let (keys, values) = Entries::object(entry.container(), len)?;
                for (key, value) in keys.zip(values) {
                    push_comparable_tag(buf, child_depth, STRING_LEVEL)?;
                    buf.extend_from_slice(key?.payload);
                    buf.push(0);
                    value?.write_comparable(child_depth, buf)?;
                }
            }
            JsonbItemType::Null => push_comparable_tag(buf, depth, NULL_LEVEL)?,
            JsonbItemType::Boolean => {
                let level = if entry.is_true() {
                    TRUE_LEVEL
                } else {
                    FALSE_LEVEL
                };
                push_comparable_tag(buf, depth, level)?;
            }
            JsonbItemType::Number => {
                push_comparable_tag(buf, depth, NUMBER_LEVEL)?;
                let n = Number::decode(entry.payload)?.as_f64();
                // `-0.0` equals `0` but has different bits; encode them alike.
                let n = if n == 0.0 { 0.0 } else { n };
                // https://github.com/rust-lang/rust/blob/9c20b2a8cc7588decb6de25ac6a7912dcef24d65/library/core/src/num/f32.rs#L1176-L1260
                let s = n.to_bits() as i64;
                let v = s ^ (((s >> 63) as u64) >> 1) as i64;
                let mut b = v.to_be_bytes();
                // Toggle top "sign" bit to ensure consistent sort order
                b[0] ^= 0x80;
                buf.extend_from_slice(&b);
            }
            JsonbItemType::String => {
                push_comparable_tag(buf, depth, STRING_LEVEL)?;
                buf.extend_from_slice(entry.payload);
                buf.push(0);
            }
            JsonbItemType::Extension => {
                push_comparable_tag(buf, depth, EXTENSION_LEVEL)?;
                buf.extend_from_slice(entry.payload);
                buf.push(0);
            }
        }
        Ok(())
    }
}
