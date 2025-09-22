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

use std::cmp::Ordering;
use std::fmt::Display;
use std::str::FromStr;

use crate::core::ArrayBuilder;
use crate::core::ObjectBuilder;
use crate::core::Serializer;
use crate::error::Error;
use crate::error::Result;
use crate::parse_value;
use crate::RawJsonb;

/// Represents a JSONB data that owns its underlying data.
///
/// This struct provides ownership over the binary JSONB representation.
/// `OwnedJsonb` is primarily used to create JSONB data from other data types (such as JSON String).
/// However, for most operations, it's necessary to convert an `OwnedJsonb` to a `RawJsonb` using the `as_raw()` method
/// to avoid unnecessary copying and to take advantage of the performance benefits of the read-only access of the `RawJsonb`.
#[derive(Debug, Clone)]
pub struct OwnedJsonb {
    /// The underlying `Vec<u8>` containing the binary JSONB data.
    pub(crate) data: Vec<u8>,
}

impl OwnedJsonb {
    /// Creates a new OwnedJsonb from a Vec<u8>.
    ///
    /// # Arguments
    ///
    /// * `data` - The `Vec<u8>` containing the JSONB data.
    ///
    /// # Returns
    ///
    /// A new `OwnedJsonb` instance.
    pub fn new(data: Vec<u8>) -> OwnedJsonb {
        Self { data }
    }

    /// Creates a `RawJsonb` view of the owned data.
    /// This is useful for passing the data to functions that expect a `RawJsonb`.
    /// This does *not* transfer ownership.
    ///
    /// # Returns
    ///
    /// A `RawJsonb` instance referencing the owned data.
    pub fn as_raw(&self) -> RawJsonb<'_> {
        RawJsonb::new(self.data.as_slice())
    }

    /// Consumes the OwnedJsonb and returns the underlying Vec<u8>.
    ///
    /// # Returns
    ///
    /// The underlying `Vec<u8>` containing the JSONB data.
    pub fn to_vec(self) -> Vec<u8> {
        self.data
    }

    /// Checks if the JSONB data is empty.
    ///
    /// # Returns
    ///
    /// `true` if the data is empty, `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the length of the JSONB data in bytes.
    ///
    /// # Returns
    ///
    /// The length of the data in bytes.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Builds a JSONB array from a collection of RawJsonb values.
    ///
    /// This function constructs a new JSONB array from an iterator of `RawJsonb` values.
    /// The resulting `OwnedJsonb` represents the binary encoding of the array.
    ///
    /// # Arguments
    ///
    /// * `items` - An iterator of `RawJsonb` values representing the elements of the array.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The newly created JSONB array.
    /// * `Err(Error)` - If any of the input `RawJsonb` values are invalid or if an error occurs during array construction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
    /// use jsonb::RawJsonb;
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
    /// let empty_array =
    ///     OwnedJsonb::build_array(<[RawJsonb<'_>; 0] as IntoIterator>::into_iter([])).unwrap();
    /// assert_eq!(empty_array.to_string(), "[]");
    ///
    /// // Example with invalid input (this will cause an error)
    /// let invalid_data = OwnedJsonb::new(vec![1, 2, 3, 4]);
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

    /// Builds a JSONB object from a collection of key-value pairs.
    ///
    /// This function constructs a new JSONB object from an iterator of key-value pairs. The keys are strings, and the values are `RawJsonb` values.
    /// The resulting `OwnedJsonb` represents the binary encoding of the object.
    ///
    /// # Arguments
    ///
    /// * `items` - An iterator of `(K, &'a RawJsonb<'a>)` tuples, where `K` is a type that can be converted into a string slice (`AsRef<str>`) representing the key,
    ///   and the second element is a `RawJsonb` representing the value.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - The newly created JSONB object.
    /// * `Err(Error)` - If any of the input `RawJsonb` values are invalid, if contain duplicate keys, or if an error occurs during object construction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
    /// use jsonb::RawJsonb;
    ///
    /// // Create some RawJsonb values
    /// let owned_num = "1".parse::<OwnedJsonb>().unwrap();
    /// let owned_str = r#""hello""#.parse::<OwnedJsonb>().unwrap();
    /// let owned_arr = "[1,2,3]".parse::<OwnedJsonb>().unwrap();
    ///
    /// // Build the object
    /// let raw_jsonbs = vec![
    ///     ("a", owned_num.as_raw()),
    ///     ("b", owned_str.as_raw()),
    ///     ("c", owned_arr.as_raw()),
    /// ];
    /// let object_result = OwnedJsonb::build_object(raw_jsonbs.into_iter());
    /// assert!(object_result.is_ok());
    /// let object = object_result.unwrap();
    ///
    /// // Convert to string for easy verification
    /// assert_eq!(object.to_string(), r#"{"a":1,"b":"hello","c":[1,2,3]}"#);
    ///
    /// // Example with an empty iterator
    /// let empty_object =
    ///     OwnedJsonb::build_object(<[(&str, RawJsonb<'_>); 0] as IntoIterator>::into_iter([]))
    ///         .unwrap();
    /// assert_eq!(empty_object.to_string(), "{}");
    ///
    /// // Example with invalid value
    /// let invalid_data = OwnedJsonb::new(vec![1, 2, 3, 4]);
    /// let result = OwnedJsonb::build_object([("a", invalid_data.as_raw())].into_iter());
    /// assert!(result.is_err());
    /// ```
    pub fn build_object<'a, K: AsRef<str>>(
        items: impl IntoIterator<Item = (K, RawJsonb<'a>)>,
    ) -> Result<OwnedJsonb> {
        let mut kvs = Vec::new();
        for (key, val) in items.into_iter() {
            kvs.push((key, val));
        }
        let mut builder = ObjectBuilder::new();
        for (key, val) in kvs.iter() {
            builder.push_raw_jsonb(key.as_ref(), *val)?;
        }
        builder.build()
    }
}

/// Creates an `OwnedJsonb` from a borrowed byte slice.  The byte slice is copied into a new `Vec<u8>`.
impl From<&[u8]> for OwnedJsonb {
    fn from(data: &[u8]) -> Self {
        Self {
            data: data.to_vec(),
        }
    }
}

/// Creates an `OwnedJsonb` from a `Vec<u8>`. This is a simple ownership transfer.
impl From<Vec<u8>> for OwnedJsonb {
    fn from(data: Vec<u8>) -> Self {
        Self { data }
    }
}

/// Parses a string into an `OwnedJsonb`.
/// The string is parsed into a JSON value, then encoded into the binary JSONB format.
impl FromStr for OwnedJsonb {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let value = parse_value(s.as_bytes())?;
        let mut data = Vec::new();
        value.write_to_vec(&mut data);
        Ok(Self { data })
    }
}

/// Allows accessing the underlying byte slice as a reference.
/// This enables easy integration with functions that expect a `&[u8]`.
impl AsRef<[u8]> for OwnedJsonb {
    fn as_ref(&self) -> &[u8] {
        self.data.as_ref()
    }
}

/// Implements the Display trait, allowing OwnedJsonb to be formatted as a string using the `{}` format specifier.
impl Display for OwnedJsonb {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let raw_jsonb = self.as_raw();
        write!(f, "{}", raw_jsonb.to_string())
    }
}

impl Eq for OwnedJsonb {}

impl PartialEq for OwnedJsonb {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

/// Implements `PartialOrd` for `OwnedJsonb`, allowing comparison of two `OwnedJsonb` values.
///
/// The comparison logic handles different JSONB types (scalar, array, object) and considers null values.
/// The ordering is defined as follows:
///
/// 1. Null is considered greater than any other type.
/// 2. Scalars are compared based on their type and value (String > Number > Boolean).
/// 3. Arrays are compared element by element.
/// 4. Objects are compared based on their keys and values.
/// 5. Arrays are greater than objects and scalars.
/// 6. Objects are greater than scalars.
/// 7. If the types are incompatible, None is returned.
#[allow(clippy::non_canonical_partial_ord_impl)]
impl PartialOrd for OwnedJsonb {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let self_raw = self.as_raw();
        let other_raw = other.as_raw();
        self_raw.partial_cmp(&other_raw)
    }
}

/// Implements `Ord` for `OwnedJsonb`, allowing comparison of two `OwnedJsonb` values using the total ordering.
/// This implementation leverages the `PartialOrd` implementation, returning `Ordering::Equal` for incomparable values.
impl Ord for OwnedJsonb {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_raw = self.as_raw();
        let other_raw = other.as_raw();
        match self_raw.partial_cmp(&other_raw) {
            Some(ordering) => ordering,
            None => Ordering::Equal,
        }
    }
}

/// Serializes a Rust data structure into an `OwnedJsonb` using Serde.
///
/// This function takes a Rust type `T` that implements the `Serialize` trait and
/// serializes it into an `OwnedJsonb`, which is a struct containing a `Vec<u8>`
/// representing the JSONB data. It uses a custom `Serializer` to handle the
/// serialization process.
///
/// # Arguments
///
/// * `value`: A reference to the value of type `T` to be serialized.
///
/// # Type Parameters
///
/// * `T`: The Rust type to serialize. This type must implement the `serde::ser::Serialize` trait.
///
/// # Returns
///
/// * `Ok(OwnedJsonb)`: If the serialization is successful, returns an `OwnedJsonb`
///   containing the serialized JSONB data.
/// * `Err(e)`: If any Serde serialization error occurs.
///
/// # Examples
///
/// ```
/// use jsonb::to_owned_jsonb;
/// use jsonb::OwnedJsonb;
/// use serde::Serialize;
///
/// #[derive(Serialize, Debug)]
/// struct Person {
///     name: String,
///     age: u32,
/// }
///
/// let person = Person {
///     name: "Bob".to_string(),
///     age: 42,
/// };
///
/// let owned_jsonb: OwnedJsonb = to_owned_jsonb(&person).unwrap();
/// assert_eq!(format!("{}", owned_jsonb), "{\"age\":42,\"name\":\"Bob\"}");
/// println!("JSONB data: {}", owned_jsonb);
/// ```
pub fn to_owned_jsonb<T>(value: &T) -> Result<OwnedJsonb>
where
    T: serde::ser::Serialize,
{
    let mut serializer = Serializer::default();
    value.serialize(&mut serializer)?;
    Ok(serializer.to_owned_jsonb())
}
