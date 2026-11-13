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

use super::constants::*;
use crate::error::Error;
use crate::error::Result;

#[derive(Clone, Debug, PartialOrd, PartialEq, Eq, Ord)]
pub(super) struct JEntry {
    pub(super) type_code: u32,
    pub(super) length: u32,
}

impl JEntry {
    /// Decodes a `JEntry` read from JSONB data.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonbJEntry` for a null or boolean `JEntry` with a
    /// non-zero length. These have no payload, and every encoder writes them
    /// with length 0. Readers that skip the payload by its length and readers
    /// that ignore it would otherwise read different values from the same bytes.
    pub(super) fn decode_jentry(encoded: u32) -> Result<JEntry> {
        let type_code = encoded & JENTRY_TYPE_MASK;
        let length = encoded & JENTRY_OFF_LEN_MASK;
        if matches!(type_code, NULL_TAG | TRUE_TAG | FALSE_TAG) && length != 0 {
            return Err(Error::InvalidJsonbJEntry);
        }
        Ok(JEntry { type_code, length })
    }

    pub(super) fn make_null_jentry() -> JEntry {
        JEntry {
            type_code: NULL_TAG,
            length: 0,
        }
    }

    pub(super) fn make_true_jentry() -> JEntry {
        JEntry {
            type_code: TRUE_TAG,
            length: 0,
        }
    }

    pub(super) fn make_false_jentry() -> JEntry {
        JEntry {
            type_code: FALSE_TAG,
            length: 0,
        }
    }

    pub(super) fn make_string_jentry(length: usize) -> Result<JEntry> {
        Self::with_length(STRING_TAG, length)
    }

    pub(super) fn make_number_jentry(length: usize) -> Result<JEntry> {
        Self::with_length(NUMBER_TAG, length)
    }

    pub(super) fn make_container_jentry(length: usize) -> Result<JEntry> {
        Self::with_length(CONTAINER_TAG, length)
    }

    pub(super) fn make_extension_jentry(length: usize) -> Result<JEntry> {
        Self::with_length(EXTENSION_TAG, length)
    }

    /// Builds a `JEntry` whose payload is `length` bytes long.
    ///
    /// # Errors
    ///
    /// Returns `Error::ValueTooLarge` if `length` does not fit the 28-bit length field.
    fn with_length(type_code: u32, length: usize) -> Result<JEntry> {
        match u32::try_from(length) {
            Ok(length) if length <= JENTRY_OFF_LEN_MASK => Ok(JEntry { type_code, length }),
            _ => Err(Error::ValueTooLarge),
        }
    }

    pub(super) fn encoded(&self) -> u32 {
        self.type_code | self.length
    }
}

/// Encodes an array or object container header holding `len` elements.
///
/// # Errors
///
/// Returns `Error::ValueTooLarge` if `len` does not fit the 29-bit length field.
pub(super) fn encode_container_header(container_tag: u32, len: usize) -> Result<u32> {
    match u32::try_from(len) {
        Ok(len) if len <= CONTAINER_HEADER_LEN_MASK => Ok(container_tag | len),
        _ => Err(Error::ValueTooLarge),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn jentry_length_must_fit_28_bits() {
        let max = JENTRY_OFF_LEN_MASK as usize;
        let jentry = JEntry::make_string_jentry(max).unwrap();
        assert_eq!(JEntry::decode_jentry(jentry.encoded()), Ok(jentry));
        assert_eq!(
            JEntry::make_string_jentry(max + 1),
            Err(Error::ValueTooLarge)
        );
        assert_eq!(
            JEntry::make_container_jentry(max + 1),
            Err(Error::ValueTooLarge)
        );
        assert_eq!(
            JEntry::make_extension_jentry(usize::MAX),
            Err(Error::ValueTooLarge)
        );
    }

    #[test]
    fn null_and_boolean_jentries_must_have_no_length() {
        for jentry in [
            JEntry::make_null_jentry(),
            JEntry::make_true_jentry(),
            JEntry::make_false_jentry(),
        ] {
            let encoded = jentry.encoded();
            assert_eq!(JEntry::decode_jentry(encoded), Ok(jentry));
            for length in [1, 2, JENTRY_OFF_LEN_MASK] {
                assert_eq!(
                    JEntry::decode_jentry(encoded | length),
                    Err(Error::InvalidJsonbJEntry),
                    "{encoded:#x} with length {length}"
                );
            }
        }
    }

    #[test]
    fn container_header_length_must_fit_29_bits() {
        let max = CONTAINER_HEADER_LEN_MASK as usize;
        let header = encode_container_header(ARRAY_CONTAINER_TAG, max).unwrap();
        assert_eq!(header & CONTAINER_HEADER_TYPE_MASK, ARRAY_CONTAINER_TAG);
        assert_eq!(
            header & CONTAINER_HEADER_LEN_MASK,
            CONTAINER_HEADER_LEN_MASK
        );
        assert_eq!(
            encode_container_header(OBJECT_CONTAINER_TAG, max + 1),
            Err(Error::ValueTooLarge)
        );
    }
}
