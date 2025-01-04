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

use std::collections::VecDeque;

use crate::builder::ArrayBuilder;
use crate::builder::ObjectBuilder;
use crate::constants::*;
use crate::error::*;
use crate::functions::core::jentry_compare_level;
use crate::functions::core::read_u32;
use crate::functions::path::get_jentry_by_name;
use crate::iterator::iterate_array;
use crate::iterator::iterate_object_entries;
use crate::jentry::JEntry;
use crate::number::Number;

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
    /// use jsonb::OwnedJsonb;
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

    /// Converts a RawJsonb value into a comparable binary representation.
    ///
    /// This function transforms the JSONB value into a new binary format designed for efficient comparison.
    /// The resulting binary data can be directly compared using byte-wise operations to determine the relative order of two JSONB values.
    /// The original JSONB data structure is flattened into a linear representation, and different data types are encoded in a way that enables direct comparison.
    /// The compare rules are the same as the `PartialOrd` trait.
    /// Scalar Null > Array > Object > Other Scalars(String > Number > Boolean).
    ///
    /// **Important:** The resulting byte array is *not* a valid JSONB format; it's specifically designed for comparison purposes and should not be interpreted as standard JSONB data.
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
