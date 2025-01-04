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

use crate::error::Error;
use crate::parse_value;
use crate::RawJsonb;
use std::fmt::Display;
use std::str::FromStr;

/// Represents a JSONB data that owns its underlying data.
///
/// This struct provides ownership over the binary JSONB representation.
/// `OwnedJsonb` is primarily used to create JSONB data from other data types (such as JSON String).
/// However, for most operations, it's necessary to convert an `OwnedJsonb` to a `RawJsonb` using the `as_raw()` method
/// to avoid unnecessary copying and to take advantage of the performance benefits of the read-only access of the `RawJsonb`.
#[derive(Debug, Clone, PartialEq)]
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

    fn from_str(s: &str) -> Result<Self, Self::Err> {
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
