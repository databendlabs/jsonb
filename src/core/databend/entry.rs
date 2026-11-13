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

//! Undecoded JSONB entries.
//!
//! [`RawEntry`] is one encoded value, and [`Entries`] walks the `JEntries` of
//! a container and yields each with its payload. Strings stay bytes, for code
//! that only compares or copies values.
//!
//! [`RawEntry::compare`] orders entries without decoding them. Strings and
//! object keys compare as bytes, without UTF-8 validation: UTF-8 orders
//! byte-wise like the characters it encodes, so the ordering matches
//! `JsonbItem`'s.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::iter::FusedIterator;

use super::constants::*;
use crate::constants::enter_container;
use crate::core::databend::util::decode_str;
use crate::core::ExtensionItem;
use crate::core::JsonbItem;
use crate::core::JsonbItemType;
use crate::core::NumberItem;
use crate::error::Error;
use crate::error::Result;
use crate::extension::ExtensionValue;
use crate::number::Number;
use crate::RawJsonb;

/// One encoded value: its `JEntry` type code and its payload bytes, borrowed
/// from JSONB data and not decoded. A container entry's payload is the whole
/// nested array or object.
///
/// Use `RawEntry` to walk encoded data where decoding would be wasted work:
/// comparison, comparable encoding, writing JSON text, serializing, and
/// decoding into `Value`. It is `Copy`, and string payloads are not checked as
/// UTF-8 until a caller needs a `&str`, so comparison orders strings by their
/// bytes and `to_string` escapes them as bytes.
///
/// [`JsonbItem`] is the general form that builders and the JSONPath selector
/// work with: it can also hold values with no encoded bytes to borrow, such as
/// owned JSONB or values computed by JSONPath filters, and its strings are
/// valid UTF-8. [`RawEntry::into_item`] converts an entry into one.
#[derive(Clone, Copy)]
pub(crate) struct RawEntry<'a> {
    /// One of the `*_TAG` type codes of a `JEntry`.
    pub(crate) type_code: u32,
    /// The encoded value: empty for null and booleans, the number, string or
    /// extension bytes for those types, and the nested JSONB for containers.
    pub(crate) payload: &'a [u8],
}

impl<'a> RawEntry<'a> {
    /// Returns the entry for the top-level value of `raw`: its scalar, or the
    /// whole array or object.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonb` for an invalid header, or for a container
    /// entry under a scalar header, which no encoder writes.
    pub(crate) fn from_jsonb(raw: RawJsonb<'a>) -> Result<Self> {
        let (header_type, _) = raw.read_header(0)?;
        match header_type {
            SCALAR_CONTAINER_TAG => {
                let entry = Entries::new(raw, 1).read_next()?;
                if entry.type_code == CONTAINER_TAG {
                    return Err(Error::InvalidJsonb);
                }
                Ok(entry)
            }
            _ => Ok(Self {
                type_code: CONTAINER_TAG,
                payload: raw.data,
            }),
        }
    }

    /// Returns the scalar this entry holds if it is a container entry wrapping
    /// a scalar header, which no encoder writes, and the entry itself otherwise.
    pub(crate) fn unwrap_scalar(self) -> Result<Self> {
        if self.type_code == CONTAINER_TAG {
            let raw = RawJsonb::new(self.payload);
            if raw.read_header(0)?.0 == SCALAR_CONTAINER_TAG {
                return Self::from_jsonb(raw);
            }
        }
        Ok(self)
    }

    /// Returns whether this entry holds `true`.
    pub(crate) fn is_true(&self) -> bool {
        self.type_code == TRUE_TAG
    }

    /// Returns whether this entry holds an array or an object.
    pub(crate) fn is_container(&self) -> bool {
        self.type_code == CONTAINER_TAG
    }

    /// The array or object this entry holds; see [`RawEntry::is_container`].
    pub(crate) fn container(&self) -> RawJsonb<'a> {
        RawJsonb::new(self.payload)
    }

    /// Decodes the entry, validating a string as UTF-8.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidUtf8` for a string payload that is not valid
    /// UTF-8, and `Error::InvalidJsonb` for an unknown `JEntry` type.
    pub(crate) fn into_item(self) -> Result<JsonbItem<'a>> {
        let payload = self.payload;
        let item = match self.type_code {
            NULL_TAG => JsonbItem::Null,
            TRUE_TAG => JsonbItem::Boolean(true),
            FALSE_TAG => JsonbItem::Boolean(false),
            NUMBER_TAG => JsonbItem::Number(NumberItem::Raw(payload)),
            STRING_TAG => JsonbItem::String(Cow::Borrowed(decode_str(payload)?)),
            EXTENSION_TAG => JsonbItem::Extension(ExtensionItem::Raw(payload)),
            CONTAINER_TAG => JsonbItem::Raw(RawJsonb::new(payload)),
            _ => return Err(Error::InvalidJsonb),
        };
        Ok(item)
    }

    /// Decodes this entry as an object key, which must be a string.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonb` if the entry is not a string, and
    /// `Error::InvalidUtf8` if it is not valid UTF-8.
    pub(crate) fn object_key(&self) -> Result<&'a str> {
        if self.type_code != STRING_TAG {
            return Err(Error::InvalidJsonb);
        }
        decode_str(self.payload)
    }

    /// Returns the type of the value this entry holds.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonb` for an unknown `JEntry` type.
    #[inline]
    pub(crate) fn item_type(&self) -> Result<JsonbItemType> {
        // Repeats the scalar arms of `RawJsonb::jsonb_item_type` instead of
        // sharing a helper, which was slower on this hot path.
        match self.type_code {
            NULL_TAG => Ok(JsonbItemType::Null),
            TRUE_TAG | FALSE_TAG => Ok(JsonbItemType::Boolean),
            NUMBER_TAG => Ok(JsonbItemType::Number),
            STRING_TAG => Ok(JsonbItemType::String),
            EXTENSION_TAG => Ok(JsonbItemType::Extension),
            CONTAINER_TAG => self.container().jsonb_item_type(),
            _ => Err(Error::InvalidJsonb),
        }
    }
}

/// Iterates over consecutive entries of a container: each `JEntry` paired
/// with its payload. Payloads follow the `JEntries` in the same order.
pub(crate) struct Entries<'a> {
    raw: RawJsonb<'a>,
    jentry_index: usize,
    payload_start: usize,
    remaining: usize,
}

impl<'a> Entries<'a> {
    /// The `count` entries right after the header of `raw`.
    ///
    /// `read_header` must have checked that `count` `JEntries` fit in `raw`.
    pub(crate) fn new(raw: RawJsonb<'a>, count: usize) -> Self {
        Self {
            raw,
            jentry_index: 4,
            payload_start: 4 + 4 * count,
            remaining: count,
        }
    }

    /// The keys of an object with `len` members.
    ///
    /// An object stores the key `JEntries`, then the value `JEntries`, then
    /// the key payloads, then the value payloads.
    pub(crate) fn keys(raw: RawJsonb<'a>, len: usize) -> Self {
        Self {
            raw,
            jentry_index: 4,
            payload_start: 4 + 8 * len,
            remaining: len,
        }
    }

    /// The keys and the values of an object with `len` members.
    ///
    /// # Errors
    ///
    /// Returns an error if a key `JEntry` lies outside the data.
    pub(crate) fn object(raw: RawJsonb<'a>, len: usize) -> Result<(Self, Self)> {
        let keys = Self::keys(raw, len);
        // The value payloads start after all key payloads.
        let mut keys_len = 0usize;
        for i in 0..len {
            keys_len = keys_len.saturating_add(raw.read_jentry(4 + 4 * i)?.length as usize);
        }
        let values = Self {
            raw,
            jentry_index: 4 + 4 * len,
            payload_start: keys.payload_start.saturating_add(keys_len),
            remaining: len,
        };
        Ok((keys, values))
    }

    /// Returns the number of entries not read yet.
    pub(crate) fn remaining(&self) -> usize {
        self.remaining
    }

    /// Ends the iteration, after an error.
    pub(super) fn stop(&mut self) {
        self.remaining = 0;
    }

    /// Reads the next entry and advances past it.
    ///
    /// # Errors
    ///
    /// Returns an error if the `JEntry` or its payload lies outside the data.
    // `#[inline]` here and on `next` lets callers in other modules, such as
    // `json_writer.rs` and `iterator.rs`, inline the walk; without it,
    // comparison and `to_string` were 5% to 20% slower with Databend's
    // `opt-level = "s"` release profile when they were in other modules.
    #[inline]
    fn read_next(&mut self) -> Result<RawEntry<'a>> {
        let jentry = self.raw.read_jentry(self.jentry_index)?;
        let payload_end = self.payload_start.saturating_add(jentry.length as usize);
        let payload = self.raw.slice(self.payload_start..payload_end)?;
        self.jentry_index += 4;
        self.payload_start = payload_end;
        Ok(RawEntry {
            type_code: jentry.type_code,
            payload,
        })
    }
}

/// Stops after the first error. Retrying would return the same error for
/// every remaining entry, since the position does not advance past it.
impl<'a> Iterator for Entries<'a> {
    type Item = Result<RawEntry<'a>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.remaining = self.remaining.checked_sub(1)?;
        let entry = self.read_next();
        if entry.is_err() {
            self.stop();
        }
        Some(entry)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl ExactSizeIterator for Entries<'_> {}

impl FusedIterator for Entries<'_> {}

impl RawEntry<'_> {
    /// Compares this value with `other` by the JSONB ordering, where `depth`
    /// is the number of containers enclosing them. Matches `JsonbItem`'s
    /// ordering.
    ///
    /// Returns `None` for incomparable or invalid values, including containers
    /// nested deeper than the recursion limit.
    pub(crate) fn compare(self, other: RawEntry<'_>, depth: usize) -> Option<Ordering> {
        let (a, b) = (self.unwrap_scalar().ok()?, other.unwrap_scalar().ok()?);
        let (a_type, b_type) = (a.item_type().ok()?, b.item_type().ok()?);
        // Different types order by type; same types return `None` here.
        if let Some(ord) = a_type.partial_cmp(&b_type) {
            return Some(ord);
        }
        match (a_type, b_type) {
            (JsonbItemType::Array(a_len), JsonbItemType::Array(b_len)) => {
                let depth = enter_container(depth).ok()?;
                let a_items = Entries::new(a.container(), a_len);
                let b_items = Entries::new(b.container(), b_len);
                for (a_item, b_item) in a_items.zip(b_items) {
                    let ord = a_item.ok()?.compare(b_item.ok()?, depth)?;
                    if ord != Ordering::Equal {
                        return Some(ord);
                    }
                }
                Some(a_len.cmp(&b_len))
            }
            (JsonbItemType::Object(a_len), JsonbItemType::Object(b_len)) => {
                let depth = enter_container(depth).ok()?;
                let (a_keys, a_values) = Entries::object(a.container(), a_len).ok()?;
                let (b_keys, b_values) = Entries::object(b.container(), b_len).ok()?;
                let a_members = a_keys.zip(a_values);
                let b_members = b_keys.zip(b_values);
                for ((a_key, a_value), (b_key, b_value)) in a_members.zip(b_members) {
                    // Keys compare as strings, by their bytes.
                    let ord = a_key.ok()?.payload.cmp(b_key.ok()?.payload);
                    if ord != Ordering::Equal {
                        return Some(ord);
                    }
                    let ord = a_value.ok()?.compare(b_value.ok()?, depth)?;
                    if ord != Ordering::Equal {
                        return Some(ord);
                    }
                }
                Some(a_len.cmp(&b_len))
            }
            (JsonbItemType::String, JsonbItemType::String) => Some(a.payload.cmp(b.payload)),
            (JsonbItemType::Number, JsonbItemType::Number) => {
                let a = Number::decode(a.payload).ok()?;
                let b = Number::decode(b.payload).ok()?;
                a.partial_cmp(&b)
            }
            (JsonbItemType::Boolean, JsonbItemType::Boolean) => Some(a.is_true().cmp(&b.is_true())),
            (JsonbItemType::Extension, JsonbItemType::Extension) => {
                let a = ExtensionValue::decode(a.payload).ok()?;
                let b = ExtensionValue::decode(b.payload).ok()?;
                a.partial_cmp(&b)
            }
            (_, _) => None,
        }
    }
}

/// A scalar entry ordered like `JsonbItem`, with incomparable values equal,
/// for use as a set element.
pub(crate) struct OrderedEntry<'a>(pub(crate) RawEntry<'a>);

impl PartialEq for OrderedEntry<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for OrderedEntry<'_> {}

impl PartialOrd for OrderedEntry<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrderedEntry<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.compare(other.0, 0).unwrap_or(Ordering::Equal)
    }
}
