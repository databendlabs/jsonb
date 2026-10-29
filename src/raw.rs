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

use crate::core::compare_entries;
use crate::core::Deserializer;
use crate::core::JsonWriter;
use crate::core::RawEntry;
use crate::error::*;
use crate::OwnedJsonb;

/// Represents JSONB data wrapped around a raw, immutable slice of bytes.
///
/// It does not own the underlying data, allowing various operations to be performed on the JSONB data *without copying*.
/// This is critical for performance when dealing with large JSONB values.
/// `RawJsonb` provides various methods to inspect and manipulate the JSONB data efficiently.
#[derive(Debug, Clone, Copy)]
pub struct RawJsonb<'a> {
    /// The underlying byte slice representing the JSONB data.
    pub(crate) data: &'a [u8],
}

impl<'a> RawJsonb<'a> {
    /// Creates a new RawJsonb from a byte slice.
    ///
    /// # Arguments
    ///
    /// * `data` - The byte slice containing the JSONB data.
    ///
    /// # Returns
    ///
    /// A new `RawJsonb` instance.
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
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

    /// Creates an `OwnedJsonb` from the `RawJsonb` by copying the underlying data.
    ///
    /// This method converts a `RawJsonb`, which holds a reference to JSONB data,
    /// into an `OwnedJsonb`, which owns its own copy of the JSONB data. This is
    /// achieved by cloning the byte slice held by the `RawJsonb` into a new `Vec<u8>`.
    ///
    /// # Returns
    ///
    /// An `OwnedJsonb` instance containing a copy of the JSONB data from the `RawJsonb`.
    pub fn to_owned(&self) -> OwnedJsonb {
        OwnedJsonb::new(self.data.to_vec())
    }

    /// Converts the JSONB value to a JSON string.
    ///
    /// This function serializes the JSONB value into a human-readable JSON string representation.
    /// If the JSONB data is invalid, treate it as a text JSON string and return directly.
    /// If the JSONB data is empty, return a JSON null for compatibility.
    ///
    /// # Returns
    ///
    /// * `String` - The JSON string representation of the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
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
    /// // Example with invalid JSONB data (fallback to treat as text JSON string)
    /// let invalid_jsonb = OwnedJsonb::new(vec![1, 2, 3, 4]); // Invalid binary JSONB
    /// let invalid_raw_jsonb = invalid_jsonb.as_raw();
    ///
    /// // It will treat as text JSON string.
    /// assert_eq!(invalid_raw_jsonb.to_string(), "\u{1}\u{2}\u{3}\u{4}");
    /// ```
    #[allow(clippy::inherent_to_string)]
    pub fn to_string(&self) -> String {
        self.write_json_text(false).unwrap_or_else(|| {
            if self.data.is_empty() {
                "null".to_string()
            } else {
                String::from_utf8_lossy(self.data).to_string()
            }
        })
    }

    /// Converts the JSONB value to a pretty-printed JSON string.
    ///
    /// This function serializes the JSONB value into a human-readable JSON string representation with indentation for formatting.
    /// If the JSONB data is invalid, return a "null" string.
    ///
    /// # Returns
    ///
    /// * `String` - The pretty-printed JSON string representation of the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::OwnedJsonb;
    ///
    /// let arr_jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = arr_jsonb.as_raw();
    /// assert_eq!(raw_jsonb.to_pretty_string(), "[\n  1,\n  2,\n  3\n]");
    ///
    /// let obj_jsonb = r#"{"a": 1, "b": "hello"}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = obj_jsonb.as_raw();
    /// assert_eq!(
    ///     raw_jsonb.to_pretty_string(),
    ///     "{\n  \"a\": 1,\n  \"b\": \"hello\"\n}"
    /// );
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
        self.write_json_text(true)
            .unwrap_or_else(|| "null".to_string())
    }

    /// Writes the value as JSON text, or returns `None` if the data is not
    /// valid JSONB or holds a string that is not valid UTF-8.
    ///
    /// The output is the same as serializing with serde_json's
    /// `CompactFormatter` or `PrettyFormatter`.
    fn write_json_text(&self, pretty: bool) -> Option<String> {
        JsonWriter::write(*self, pretty).ok()
    }
}

/// Converts a borrowed byte slice into a RawJsonb.
/// This provides a convenient way to create a RawJsonb from existing data without copying.
impl<'a> From<&'a [u8]> for RawJsonb<'a> {
    fn from(data: &'a [u8]) -> Self {
        Self { data }
    }
}

/// Allows accessing the underlying byte slice as a reference.
/// This enables easy integration with functions that expect a &[u8].
impl AsRef<[u8]> for RawJsonb<'_> {
    fn as_ref(&self) -> &[u8] {
        self.data
    }
}

impl Eq for RawJsonb<'_> {}

impl PartialEq for RawJsonb<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

/// Implements `PartialOrd` for `RawJsonb`, allowing comparison of two `RawJsonb` values.
///
/// The comparison logic handles different JSONB types (scalar, array, object) and considers null values.
/// The ordering is defined as follows:
///
/// 1. Null is considered greater than any other type.
/// 2. Scalars are compared based on their type and value (String > Number > Boolean > ExtensionValue).
/// 3. Arrays are compared element by element.
/// 4. Objects are compared based on their keys and values.
/// 5. Arrays are greater than objects and scalars.
/// 6. Objects are greater than scalars.
/// 7. If the types are incompatible, None is returned.
#[allow(clippy::non_canonical_partial_ord_impl)]
impl PartialOrd for RawJsonb<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.partial_cmp_with_depth(other, 0)
    }
}

impl RawJsonb<'_> {
    /// Compares two values, where `depth` is the number of enclosing containers.
    ///
    /// Returns `None` for incomparable values, including containers nested
    /// deeper than the recursion limit.
    pub(crate) fn partial_cmp_with_depth(&self, other: &Self, depth: usize) -> Option<Ordering> {
        let a = RawEntry::from_jsonb(*self).ok()?;
        let b = RawEntry::from_jsonb(*other).ok()?;
        compare_entries(a, b, depth)
    }
}

/// Implements `Ord` for `RawJsonb`, allowing comparison of two `RawJsonb` values using the total ordering.
/// This implementation leverages the `PartialOrd` implementation, returning `Ordering::Equal` for incomparable values.
impl Ord for RawJsonb<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ordering) => ordering,
            None => Ordering::Equal,
        }
    }
}

/// Deserializes a `RawJsonb` into a Rust data structure using Serde.
///
/// This function takes a `RawJsonb` (a borrowed slice of JSONB data) and attempts
/// to deserialize it into a Rust type `T` that implements the `Deserialize` trait.
/// It uses a custom `Deserializer` to handle the JSONB data.
///
/// # Arguments
///
/// * `raw_jsonb`: A reference to the `RawJsonb` containing the JSONB data to deserialize.
///
/// # Type Parameters
///
/// * `T`: The Rust type to deserialize the JSONB data into.  This type must implement
///   the `serde::de::Deserialize` trait.
///
/// # Returns
///
/// * `Ok(t)`: If the deserialization is successful, returns the deserialized value of type `T`.
/// * `Err(Error::InvalidJsonb)`: If the deserialization fails due to invalid JSONB data
///   (e.g., trailing characters after the expected JSONB structure).
/// * `Err(e)`: If any other Serde deserialization error occurs.
///
/// # Examples
///
/// ```
/// use jsonb::from_raw_jsonb;
/// use jsonb::OwnedJsonb;
/// use jsonb::RawJsonb;
/// use serde::Deserialize;
///
/// #[derive(Deserialize, Debug, PartialEq, Eq)]
/// struct Person {
///     name: String,
///     age: u32,
/// }
///
/// let owned_jsonb = r#"{"name": "Alice", "age": 20}"#.parse::<OwnedJsonb>().unwrap();
/// let raw_jsonb = owned_jsonb.as_raw();
///
/// let person: Person = from_raw_jsonb(&raw_jsonb).unwrap();
/// assert_eq!(person, Person { name: "Alice".to_string(), age: 20 });
/// println!("{:?}", person); // Output: Person { name: "Alice", age: 20 }
/// ```
pub fn from_raw_jsonb<'de, T>(raw_jsonb: &'de RawJsonb) -> Result<T>
where
    T: serde::de::Deserialize<'de>,
{
    let mut deserializer = Deserializer::new(raw_jsonb);
    let t = T::deserialize(&mut deserializer)?;
    if deserializer.end() {
        Ok(t)
    } else {
        // Trailing characters
        Err(Error::InvalidJsonb)
    }
}
