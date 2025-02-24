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

// This file contains functions that specifically operate on JSONB array values.

use crate::core::ArrayBuilder;
use crate::core::ArrayDistinctBuilder;
use crate::core::ArrayIterator;

use crate::error::*;

use crate::OwnedJsonb;
use crate::RawJsonb;
use crate::ValueType;

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
        raw_jsonbs: impl IntoIterator<Item = RawJsonb<'a>>,
    ) -> Result<OwnedJsonb> {
        let mut builder = ArrayBuilder::new();
        for raw_jsonb in raw_jsonbs.into_iter() {
            builder.push_raw_jsonb(raw_jsonb);
        }
        builder.build()
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
    /// use jsonb::OwnedJsonb;
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
    pub fn array_length(&self) -> Result<Option<usize>> {
        let value_type = self.value_type()?;
        if let ValueType::Array(len) = value_type {
            Ok(Some(len))
        } else {
            Ok(None)
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
    /// use jsonb::OwnedJsonb;
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
    pub fn array_values(&self) -> Result<Option<Vec<OwnedJsonb>>> {
        let array_iter_opt = ArrayIterator::new(*self)?;
        match array_iter_opt {
            Some(mut array_iter) => {
                let mut values = Vec::with_capacity(array_iter.len());
                for item_result in &mut array_iter {
                    let item = item_result?;
                    let value = OwnedJsonb::from_item(item)?;
                    values.push(value);
                }
                Ok(Some(values))
            }
            None => Ok(None),
        }
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
    /// use jsonb::OwnedJsonb;
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
    pub fn array_distinct(&self) -> Result<OwnedJsonb> {
        let array_iter_opt = ArrayIterator::new(*self)?;
        match array_iter_opt {
            Some(mut array_iter) => {
                let mut builder = ArrayDistinctBuilder::new(array_iter.len());
                for item_result in &mut array_iter {
                    let item = item_result?;
                    builder.push_raw_jsonb_item(item);
                }
                builder.build()
            }
            None => {
                let mut builder = ArrayBuilder::with_capacity(1);
                builder.push_raw_jsonb(*self);
                builder.build()
            }
        }
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
    /// use jsonb::OwnedJsonb;
    ///
    /// // Array intersection
    /// let arr1 = r#"[1, 2, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[2, 3, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// let intersection = arr1.as_raw().array_intersection(&arr2.as_raw()).unwrap();
    /// assert_eq!(intersection.to_string(), "[2,3]"); // Order may vary, duplicates handled
    ///
    /// let arr1 = r#"[1, 1, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[1, 1, 1, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let intersection = arr1.as_raw().array_intersection(&arr2.as_raw()).unwrap();
    /// assert_eq!(intersection.to_string(), "[1,1,3]"); //Order may vary
    ///
    /// // Object containment (checks for complete equality)
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let contained = obj1.as_raw().array_intersection(&obj2.as_raw()).unwrap();
    /// assert_eq!(contained.to_string(), r#"[{"a":1}]"#);
    ///
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// let contained = obj1.as_raw().array_intersection(&obj2.as_raw()).unwrap();
    /// assert_eq!(contained.to_string(), "[]"); // Not contained
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "1".parse::<OwnedJsonb>().unwrap();
    /// let contained = scalar1.as_raw().array_intersection(&scalar2.as_raw()).unwrap();
    /// assert_eq!(contained.to_string(), "[1]"); // Contained
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "2".parse::<OwnedJsonb>().unwrap();
    /// let contained = scalar1.as_raw().array_intersection(&scalar2.as_raw()).unwrap();
    /// assert_eq!(contained.to_string(), "[]"); // Not contained
    /// ```
    pub fn array_intersection(&self, other: &RawJsonb) -> Result<OwnedJsonb> {
        let other_array_iter_opt = ArrayIterator::new(*other)?;
        let mut other_builder = match other_array_iter_opt {
            Some(mut array_iter) => {
                let mut builder = ArrayDistinctBuilder::new(array_iter.len());
                for item_result in &mut array_iter {
                    let item = item_result?;
                    builder.push_raw_jsonb_item(item);
                }
                builder
            }
            None => {
                let mut builder = ArrayDistinctBuilder::new(1);
                builder.push_raw_jsonb(*other);
                builder
            }
        };

        let array_iter_opt = ArrayIterator::new(*self)?;
        match array_iter_opt {
            Some(mut array_iter) => {
                let mut builder = ArrayBuilder::with_capacity(array_iter.len());
                for item_result in &mut array_iter {
                    let item = item_result?;
                    if other_builder.pop_raw_jsonb_item(item.clone()).is_some() {
                        builder.push_raw_jsonb_item(item);
                    }
                }
                builder.build()
            }
            None => {
                let mut builder = ArrayBuilder::with_capacity(1);
                if other_builder.pop_raw_jsonb(*self).is_some() {
                    builder.push_raw_jsonb(*self);
                }
                builder.build()
            }
        }
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
    /// use jsonb::OwnedJsonb;
    ///
    /// // Array except
    /// let arr1 = r#"[1, 2, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[2, 3, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// let except = arr1.as_raw().array_except(&arr2.as_raw()).unwrap();
    /// assert_eq!(except.to_string(), "[1,2]"); // Order may vary, duplicates handled
    ///
    /// let arr1 = r#"[1, 1, 2, 3, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[1, 3, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let except = arr1.as_raw().array_except(&arr2.as_raw()).unwrap();
    /// assert_eq!(except.to_string(), "[1,2]"); // Order may vary
    ///
    /// // Object non-containment
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let not_contained = obj1.as_raw().array_except(&obj2.as_raw()).unwrap();
    /// assert_eq!(not_contained.to_string(), "[]"); // Completely contained
    ///
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// let not_contained = obj1.as_raw().array_except(&obj2.as_raw()).unwrap();
    /// assert_eq!(not_contained.to_string(), r#"[{"a":1}]"#); // Not contained
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "1".parse::<OwnedJsonb>().unwrap();
    /// let not_contained = scalar1.as_raw().array_except(&scalar2.as_raw()).unwrap();
    /// assert_eq!(not_contained.to_string(), "[]"); // Contained
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "2".parse::<OwnedJsonb>().unwrap();
    /// let not_contained = scalar1.as_raw().array_except(&scalar2.as_raw()).unwrap();
    /// assert_eq!(not_contained.to_string(), "[1]"); // Not contained
    /// ```
    pub fn array_except(&self, other: &RawJsonb) -> Result<OwnedJsonb> {
        let other_array_iter_opt = ArrayIterator::new(*other)?;
        let mut other_builder = match other_array_iter_opt {
            Some(mut array_iter) => {
                let mut builder = ArrayDistinctBuilder::new(array_iter.len());
                for item_result in &mut array_iter {
                    let item = item_result?;
                    builder.push_raw_jsonb_item(item);
                }
                builder
            }
            None => {
                let mut builder = ArrayDistinctBuilder::new(1);
                builder.push_raw_jsonb(*other);
                builder
            }
        };

        let array_iter_opt = ArrayIterator::new(*self)?;
        match array_iter_opt {
            Some(mut array_iter) => {
                let mut builder = ArrayBuilder::with_capacity(array_iter.len());
                for item_result in &mut array_iter {
                    let item = item_result?;
                    if other_builder.pop_raw_jsonb_item(item.clone()).is_none() {
                        builder.push_raw_jsonb_item(item);
                    }
                }
                builder.build()
            }
            None => {
                let mut builder = ArrayBuilder::with_capacity(1);
                if other_builder.pop_raw_jsonb(*self).is_none() {
                    builder.push_raw_jsonb(*self);
                }
                builder.build()
            }
        }
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
    /// use jsonb::OwnedJsonb;
    ///
    /// // Array overlap
    /// let arr1 = r#"[1, 2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[3, 4, 5]"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(arr1.as_raw().array_overlap(&arr2.as_raw()).unwrap()); // True because of '3'
    ///
    /// let arr1 = r#"[1, 2]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[3, 4]"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(!arr1.as_raw().array_overlap(&arr2.as_raw()).unwrap()); // False, no common elements
    ///
    /// let arr1 = r#"[1, 2, 2]"#.parse::<OwnedJsonb>().unwrap();
    /// let arr2 = r#"[2, 3]"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(arr1.as_raw().array_overlap(&arr2.as_raw()).unwrap()); // True, '2' is common
    ///
    /// // Object/scalar overlap (requires complete equality for true)
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(obj1.as_raw().array_overlap(&obj2.as_raw()).unwrap()); // True, completely equal
    ///
    /// let obj1 = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let obj2 = r#"{"a": 2}"#.parse::<OwnedJsonb>().unwrap();
    /// assert!(!obj1.as_raw().array_overlap(&obj2.as_raw()).unwrap()); // False, not equal
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "1".parse::<OwnedJsonb>().unwrap();
    /// assert!(scalar1.as_raw().array_overlap(&scalar2.as_raw()).unwrap()); // True, equal
    ///
    /// let scalar1 = "1".parse::<OwnedJsonb>().unwrap();
    /// let scalar2 = "2".parse::<OwnedJsonb>().unwrap();
    /// assert!(!scalar1.as_raw().array_overlap(&scalar2.as_raw()).unwrap()); // False, not equal
    ///
    /// // Invalid input
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    /// let result = invalid_raw_jsonb.array_overlap(&arr1.as_raw());
    /// assert!(result.is_err()); // Returns an error
    /// ```
    pub fn array_overlap(&self, other: &RawJsonb) -> Result<bool> {
        let other_array_iter_opt = ArrayIterator::new(*other)?;
        let mut other_builder = match other_array_iter_opt {
            Some(mut array_iter) => {
                let mut builder = ArrayDistinctBuilder::new(array_iter.len());
                for item_result in &mut array_iter {
                    let item = item_result?;
                    builder.push_raw_jsonb_item(item);
                }
                builder
            }
            None => {
                let mut builder = ArrayDistinctBuilder::new(1);
                builder.push_raw_jsonb(*other);
                builder
            }
        };

        let array_iter_opt = ArrayIterator::new(*self)?;
        match array_iter_opt {
            Some(mut array_iter) => {
                for item_result in &mut array_iter {
                    let item = item_result?;
                    if other_builder.pop_raw_jsonb_item(item).is_some() {
                        return Ok(true);
                    }
                }
            }
            None => {
                if other_builder.pop_raw_jsonb(*self).is_some() {
                    return Ok(true);
                }
            }
        }
        Ok(false)
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
    /// use jsonb::OwnedJsonb;
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// let new_jsonb = "4".parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    ///
    /// // Insert at index 1
    /// let inserted = raw_jsonb.array_insert(1, &new_raw_jsonb).unwrap();
    /// assert_eq!(inserted.to_string(), "[1,4,2,3]");
    ///
    /// // Insert at the beginning (pos = 0)
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.array_insert(0, &new_raw_jsonb).unwrap();
    /// assert_eq!(inserted.to_string(), "[4,1,2,3]");
    ///
    /// // Insert at the end (pos >= length)
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.array_insert(10, &new_raw_jsonb).unwrap();
    /// assert_eq!(inserted.to_string(), "[1,2,3,4]");
    ///
    /// // Insert into an object
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// let new_jsonb = "2".parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.array_insert(0, &new_raw_jsonb);
    /// assert_eq!(inserted.unwrap().to_string(), r#"[2,{"a":1}]"#);
    ///
    /// // Insert into a scalar
    /// let scalar_jsonb = "1".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = scalar_jsonb.as_raw();
    /// let new_jsonb = "2".parse::<OwnedJsonb>().unwrap();
    /// let new_raw_jsonb = new_jsonb.as_raw();
    /// let inserted = raw_jsonb.array_insert(0, &new_raw_jsonb);
    /// assert_eq!(inserted.unwrap().to_string(), "[2,1]");
    /// ```
    pub fn array_insert(&self, pos: i32, new_val: &RawJsonb) -> Result<OwnedJsonb> {
        let len = self.array_length()?.unwrap_or(1);

        let idx = if pos < 0 { len as i32 - pos.abs() } else { pos };
        let idx = if idx < 0 {
            0
        } else if idx > len as i32 {
            len
        } else {
            idx as usize
        };

        let mut builder = ArrayBuilder::with_capacity(len + 1);
        let array_iter_opt = ArrayIterator::new(*self)?;
        match array_iter_opt {
            Some(mut array_iter) => {
                let mut i = 0;
                for item_result in &mut array_iter {
                    let item = item_result?;
                    if i == idx {
                        builder.push_raw_jsonb(*new_val);
                    }
                    builder.push_raw_jsonb_item(item);
                    i += 1;
                }
                if i == idx {
                    builder.push_raw_jsonb(*new_val);
                }
            }
            None => {
                if idx == 0 {
                    builder.push_raw_jsonb(*new_val);
                    builder.push_raw_jsonb(*self);
                } else {
                    builder.push_raw_jsonb(*self);
                    builder.push_raw_jsonb(*new_val);
                }
            }
        }
        builder.build()
    }
}
