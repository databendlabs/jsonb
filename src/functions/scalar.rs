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

// This file contains functions that specifically operate on JSONB scalar values.

use std::borrow::Cow;

use crate::core::JsonbItemType;
use crate::error::*;
use crate::from_raw_jsonb;
use crate::number::Number;
use crate::RawJsonb;

impl RawJsonb<'_> {
    /// Checks if the JSONB value is null.
    ///
    /// This function determines whether the JSONB value represents a JSON `null`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` if the value is null.
    /// * `Ok(false)` if the value is not null.
    /// * `Err(Error)` - If the input JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
    ///
    /// let null_jsonb = "null".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = null_jsonb.as_raw();
    /// assert!(raw_jsonb.is_null().unwrap());
    ///
    /// let obj_jsonb = r#"{"a": 1}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// assert!(!raw_jsonb.is_null().unwrap());
    /// ```
    pub fn is_null(&self) -> Result<bool> {
        let jsonb_item_type = self.jsonb_item_type()?;
        Ok(matches!(jsonb_item_type, JsonbItemType::Null))
    }

    /// Extracts a null value from a JSONB value.
    ///
    /// This function returns `Some(())` if the value is null and `None` otherwise.
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
    /// use jsonb::OwnedJsonb;
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
    pub fn as_null(&self) -> Result<Option<()>> {
        let res: Result<()> = from_raw_jsonb(self);
        match res {
            Ok(_) => Ok(Some(())),
            Err(Error::UnexpectedType) => Ok(None),
            Err(e) => Err(e),
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
    /// use jsonb::OwnedJsonb;
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
    pub fn is_boolean(&self) -> Result<bool> {
        let jsonb_item_type = self.jsonb_item_type()?;
        Ok(matches!(jsonb_item_type, JsonbItemType::Boolean))
    }

    /// Extracts a boolean value from a JSONB value.
    ///
    /// This function attempts to extract a boolean value (`true` or `false`) from the JSONB value.
    /// If the JSONB value is a boolean, the corresponding boolean value is returned, and return `None` otherwise.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(true))` - If the value is JSON `true`.
    /// * `Ok(Some(false))` - If the value is JSON `false`.
    /// * `Ok(None)` - If the value is not a boolean.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn as_bool(&self) -> Result<Option<bool>> {
        let res: Result<bool> = from_raw_jsonb(self);
        match res {
            Ok(v) => Ok(Some(v)),
            Err(Error::UnexpectedType) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Converts a JSONB value to a boolean.
    ///
    /// This function attempts to convert a JSONB value to a boolean. It prioritizes extracting a boolean value directly if possible.
    /// If the value is a string, it converts the string to lowercase and checks if it's "true" or "false". Otherwise, it returns an error.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the value is JSON `true` or a string that is "true" (case-insensitive).
    /// * `Ok(false)` - If the value is JSON `false` or a string that is "false" (case-insensitive).
    /// * `Err(Error::InvalidCast)` - If the value cannot be converted to a boolean.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn to_bool(&self) -> Result<bool> {
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
    /// use jsonb::OwnedJsonb;
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
    pub fn is_number(&self) -> Result<bool> {
        let jsonb_item_type = self.jsonb_item_type()?;
        Ok(matches!(jsonb_item_type, JsonbItemType::Number))
    }

    /// Extracts a number from a JSONB value.
    ///
    /// This function attempts to extract a number from the JSONB value.
    /// If the JSONB value is a number, it returns the number; otherwise, it returns `None`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(Number))` - If the value is a number, the extracted number.
    /// * `Ok(None)` - If the value is not a number.
    /// * `Err(Error)` - If the JSONB data is invalid or if the number cannot be decoded.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::Number;
    /// use jsonb::OwnedJsonb;
    /// use jsonb::RawJsonb;
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
    /// assert!(result.is_err()); // Decodes should return Err
    /// ```
    pub fn as_number(&self) -> Result<Option<Number>> {
        if let Some(v) = self.as_u64()? {
            Ok(Some(Number::UInt64(v)))
        } else if let Some(v) = self.as_i64()? {
            Ok(Some(Number::Int64(v)))
        } else if let Some(v) = self.as_f64()? {
            Ok(Some(Number::Float64(v)))
        } else {
            Ok(None)
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
    /// use jsonb::OwnedJsonb;
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
    pub fn is_i64(&self) -> Result<bool> {
        self.as_i64().map(|v| v.is_some())
    }

    /// Extracts an i64 integer from a JSONB value.
    ///
    /// This function attempts to extract an `i64` integer from the JSONB value.
    /// If the JSONB value is a number and can be represented as an `i64` without loss of information, the integer value is returned.
    /// Otherwise, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(i64))` - If the value is an integer that can be represented as an `i64`.
    /// * `Ok(None)` - If the value is not an integer or cannot be represented as an `i64`.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn as_i64(&self) -> Result<Option<i64>> {
        let res: Result<i64> = from_raw_jsonb(self);
        match res {
            Ok(v) => Ok(Some(v)),
            Err(Error::UnexpectedType) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Converts a JSONB value to an i64 integer.
    ///
    /// This function attempts to convert a JSONB value to an `i64` integer.
    /// It prioritizes direct conversion from a number if possible.
    /// If the value is a boolean, it's converted to 1 (for `true`) or 0 (for `false`).
    /// If the value is a string that can be parsed as an `i64`, that parsed value is returned.
    /// Otherwise, an error is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(i64)` - The `i64` representation of the JSONB value.
    /// * `Err(Error::InvalidCast)` - If the value cannot be converted to an `i64`.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn to_i64(&self) -> Result<i64> {
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
    /// This function checks if the JSONB value is a number and can be converted to a `u64` without loss of information.
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
    /// use jsonb::OwnedJsonb;
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
    pub fn is_u64(&self) -> Result<bool> {
        self.as_u64().map(|v| v.is_some())
    }

    /// Extracts a u64 unsigned integer from a JSONB value.
    ///
    /// This function attempts to extract a `u64` unsigned integer from the JSONB value.
    /// If the JSONB value is a number and can be represented as a `u64` without loss of information (i.e., it's a non-negative integer within the `u64` range),
    /// the unsigned integer value is returned. Otherwise, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(u64))` - If the value is an unsigned integer that can be represented as a `u64`.
    /// * `Ok(None)` - If the value is not an unsigned integer or cannot be represented as a `u64`.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn as_u64(&self) -> Result<Option<u64>> {
        let res: Result<u64> = from_raw_jsonb(self);
        match res {
            Ok(v) => Ok(Some(v)),
            Err(Error::UnexpectedType) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Converts a JSONB value to a u64 unsigned integer.
    ///
    /// This function attempts to convert a JSONB value to a `u64` unsigned integer.
    /// It prioritizes direct conversion from a number if possible.
    /// If the value is a boolean, it's converted to 1 (for `true`) or 0 (for `false`).
    /// If the value is a string that can be parsed as a `u64`, that parsed value is returned.
    /// Otherwise, an error is returned.
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
    /// use jsonb::OwnedJsonb;
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
    pub fn to_u64(&self) -> Result<u64> {
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
    /// This function checks if the JSONB value is a number and can be converted to an `f64` without loss of information
    /// (this is generally always true for numbers in JSONB).
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
    /// use jsonb::OwnedJsonb;
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
    pub fn is_f64(&self) -> Result<bool> {
        self.as_f64().map(|v| v.is_some())
    }

    /// Extracts an f64 floating-point number from a JSONB value.
    ///
    /// This function attempts to extract an `f64` floating-point number from the JSONB value.
    /// If the JSONB value is a number, it's converted to an `f64` and returned. Otherwise, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(f64))` - If the value is a number, the extracted `f64` value.
    /// * `Ok(None)` - If the value is not a number.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn as_f64(&self) -> Result<Option<f64>> {
        let res: Result<f64> = from_raw_jsonb(self);
        match res {
            Ok(v) => Ok(Some(v)),
            Err(Error::UnexpectedType) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Converts a JSONB value to an f64 floating-point number.
    ///
    /// This function attempts to convert a JSONB value to an `f64` floating-point number.
    /// It prioritizes direct conversion from a number if possible.
    /// If the value is a boolean, it's converted to 1.0 (for `true`) or 0.0 (for `false`).
    /// If the value is a string that can be parsed as an `f64`, that parsed value is returned.
    /// Otherwise, an error is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONB value.
    ///
    /// # Returns
    ///
    /// * `Ok(f64)` - The `f64` representation of the JSONB value.
    /// * `Err(Error::InvalidCast)` - If the value cannot be converted to an `f64`
    ///   (e.g., it's an array, an object, a string that is not a valid number, or a null value).
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn to_f64(&self) -> Result<f64> {
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
    /// use jsonb::OwnedJsonb;
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
    pub fn is_string(&self) -> Result<bool> {
        let jsonb_item_type = self.jsonb_item_type()?;
        Ok(matches!(jsonb_item_type, JsonbItemType::String))
    }

    /// Extracts a string from a JSONB value.
    ///
    /// This function attempts to extract a string from the JSONB value.
    /// If the JSONB value is a string, it returns the string as a `Cow<'_, str>`.
    /// Otherwise, it returns `None`.
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
    /// use jsonb::OwnedJsonb;
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
    pub fn as_str(&self) -> Result<Option<Cow<'_, str>>> {
        let res: Result<String> = from_raw_jsonb(self);
        match res {
            Ok(v) => Ok(Some(Cow::Owned(v))),
            Err(Error::UnexpectedType) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Converts a JSONB value to a String.
    ///
    /// This function attempts to convert a JSONB value to a string representation.
    /// It prioritizes direct conversion from strings.
    /// Booleans are converted to "true" or "false", and numbers are converted to their string representations.
    /// Other types (arrays, objects, null) will result in an error.
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
    /// use jsonb::OwnedJsonb;
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
    pub fn to_str(&self) -> Result<String> {
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
    /// * `Ok(false)` - If the value is not an array.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn is_array(&self) -> Result<bool> {
        let jsonb_item_type = self.jsonb_item_type()?;
        Ok(matches!(jsonb_item_type, JsonbItemType::Array(_)))
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
    /// * `Ok(false)` - If the value is not an object.
    /// * `Err(Error)` - If the JSONB data is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    pub fn is_object(&self) -> Result<bool> {
        let jsonb_item_type = self.jsonb_item_type()?;
        Ok(matches!(jsonb_item_type, JsonbItemType::Object(_)))
    }
}
