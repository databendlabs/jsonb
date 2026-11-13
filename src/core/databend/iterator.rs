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

//! Iteration over the entries of JSONB containers.
//!
//! [`Entries`] walks the `JEntries` of a container and yields each with its
//! payload as an undecoded [`RawEntry`]; strings stay bytes, for code that only
//! compares or copies values. The other iterators decode those entries into
//! `JsonbItem`s, validating strings as UTF-8.

use std::borrow::Cow;
use std::iter::FusedIterator;

use super::constants::*;
use crate::core::databend::util::decode_str;
use crate::core::ExtensionItem;
use crate::core::JsonbItem;
use crate::core::JsonbItemType;
use crate::core::NumberItem;
use crate::error::Error;
use crate::error::Result;
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
    fn stop(&mut self) {
        self.remaining = 0;
    }

    /// Reads the next entry and advances past it.
    ///
    /// # Errors
    ///
    /// Returns an error if the `JEntry` or its payload lies outside the data.
    // `#[inline]` here and on `next` lets callers in other modules, such as
    // `compare.rs` and `json_writer.rs`, inline the walk; without it,
    // comparison and `to_string` were 5% to 20% slower with Databend's
    // `opt-level = "s"` release profile.
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

/// Implements `Iterator`, `ExactSizeIterator` and `FusedIterator` for an
/// iterator with `read_next`, `remaining` and `stop` methods.
///
/// The iterator stops after the first error, including an error decoding an
/// entry that `Entries` read successfully. Retrying would return the same
/// error forever, and `nth`/`count` would then loop over every remaining index.
macro_rules! impl_fused_iterator {
    ($iter:ident, $item:ty) => {
        impl<'a> Iterator for $iter<'a> {
            type Item = Result<$item>;

            fn next(&mut self) -> Option<Self::Item> {
                let item = self.read_next()?;
                if item.is_err() {
                    self.stop();
                }
                Some(item)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                let remaining = self.remaining();
                (remaining, Some(remaining))
            }
        }

        impl ExactSizeIterator for $iter<'_> {}

        impl FusedIterator for $iter<'_> {}
    };
}

/// Iterates over the elements of an array, decoded.
pub(crate) struct ArrayIterator<'a> {
    entries: Entries<'a>,
    length: usize,
}

impl<'a> ArrayIterator<'a> {
    pub(crate) fn new(raw_jsonb: RawJsonb<'a>) -> Result<Option<Self>> {
        let (header_type, header_len) = raw_jsonb.read_header(0)?;
        if header_type == ARRAY_CONTAINER_TAG {
            Ok(Some(Self::new_with_len(raw_jsonb, header_len)))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn new_with_len(raw_jsonb: RawJsonb<'a>, length: usize) -> Self {
        Self {
            entries: Entries::new(raw_jsonb, length),
            length,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.length
    }

    /// Returns the element at `index` among the remaining ones, or the first
    /// error among the elements before it.
    ///
    /// `Iterator::nth` would discard those errors, and since the iterator stops
    /// after an error it would then return `None` for an index in range.
    pub(crate) fn get(mut self, index: usize) -> Result<Option<JsonbItem<'a>>> {
        // Return at once past the end, so `usize::MAX` reads nothing.
        if index >= self.remaining() {
            return Ok(None);
        }
        for item in self.by_ref().take(index) {
            item?;
        }
        self.next().transpose()
    }

    fn read_next(&mut self) -> Option<Result<JsonbItem<'a>>> {
        Some(self.entries.next()?.and_then(RawEntry::into_item))
    }

    fn remaining(&self) -> usize {
        self.entries.remaining()
    }

    fn stop(&mut self) {
        self.entries.stop();
    }
}

impl_fused_iterator!(ArrayIterator, JsonbItem<'a>);

/// Iterates over the keys of an object, decoded.
pub(crate) struct ObjectKeyIterator<'a> {
    keys: Entries<'a>,
    length: usize,
}

impl<'a> ObjectKeyIterator<'a> {
    pub(crate) fn new(raw_jsonb: RawJsonb<'a>) -> Result<Option<Self>> {
        let (header_type, header_len) = raw_jsonb.read_header(0)?;
        if header_type == OBJECT_CONTAINER_TAG {
            Ok(Some(Self {
                keys: Entries::keys(raw_jsonb, header_len),
                length: header_len,
            }))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.length
    }

    fn read_next(&mut self) -> Option<Result<JsonbItem<'a>>> {
        Some(self.keys.next()?.and_then(RawEntry::into_item))
    }

    fn remaining(&self) -> usize {
        self.keys.remaining()
    }

    fn stop(&mut self) {
        self.keys.stop();
    }
}

impl_fused_iterator!(ObjectKeyIterator, JsonbItem<'a>);

/// Iterates over the values of an object, decoded.
pub(crate) struct ObjectValueIterator<'a> {
    values: Entries<'a>,
    length: usize,
}

impl<'a> ObjectValueIterator<'a> {
    pub(crate) fn new(raw_jsonb: RawJsonb<'a>) -> Result<Option<Self>> {
        let (header_type, header_len) = raw_jsonb.read_header(0)?;
        if header_type == OBJECT_CONTAINER_TAG {
            let (_, values) = Entries::object(raw_jsonb, header_len)?;
            Ok(Some(Self {
                values,
                length: header_len,
            }))
        } else {
            Ok(None)
        }
    }

    #[allow(dead_code)]
    pub(crate) fn len(&self) -> usize {
        self.length
    }

    fn read_next(&mut self) -> Option<Result<JsonbItem<'a>>> {
        Some(self.values.next()?.and_then(RawEntry::into_item))
    }

    fn remaining(&self) -> usize {
        self.values.remaining()
    }

    fn stop(&mut self) {
        self.values.stop();
    }
}

impl_fused_iterator!(ObjectValueIterator, JsonbItem<'a>);

/// Iterates over the members of an object: each key, as a string, with its
/// value decoded.
pub(crate) struct ObjectIterator<'a> {
    keys: Entries<'a>,
    values: Entries<'a>,
    length: usize,
}

impl<'a> ObjectIterator<'a> {
    pub(crate) fn new(raw_jsonb: RawJsonb<'a>) -> Result<Option<Self>> {
        let (header_type, header_len) = raw_jsonb.read_header(0)?;
        if header_type == OBJECT_CONTAINER_TAG {
            Ok(Some(Self::new_with_len(raw_jsonb, header_len)?))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn new_with_len(raw_jsonb: RawJsonb<'a>, length: usize) -> Result<Self> {
        let (keys, values) = Entries::object(raw_jsonb, length)?;
        Ok(Self {
            keys,
            values,
            length,
        })
    }

    pub(crate) fn len(&self) -> usize {
        self.length
    }

    fn read_next(&mut self) -> Option<Result<(&'a str, JsonbItem<'a>)>> {
        let key = self.keys.next()?.and_then(|key| decode_str(key.payload));
        let value = self.values.next()?;
        Some(key.and_then(|key| Ok((key, value?.into_item()?))))
    }

    fn remaining(&self) -> usize {
        self.keys.remaining()
    }

    fn stop(&mut self) {
        self.keys.stop();
        self.values.stop();
    }
}

impl_fused_iterator!(ObjectIterator, (&'a str, JsonbItem<'a>));

#[cfg(test)]
mod tests {
    use super::*;
    use crate::OwnedJsonb;

    fn owned(json: &str) -> OwnedJsonb {
        json.parse().unwrap()
    }

    fn number_string(item: JsonbItem<'_>) -> String {
        match item {
            JsonbItem::Number(value) => value.as_number().unwrap().to_string(),
            _ => panic!("expected number item"),
        }
    }

    fn string_value(item: JsonbItem<'_>) -> String {
        item.as_str().unwrap().into_owned()
    }

    #[test]
    fn array_iterator_reports_exact_remaining_items() {
        let jsonb = owned(r#"[1,"two",true,null]"#);
        let mut iter = ArrayIterator::new(jsonb.as_raw()).unwrap().unwrap();

        assert_eq!(iter.len(), 4);
        assert_eq!(iter.size_hint(), (4, Some(4)));
        assert_eq!(number_string(iter.next().unwrap().unwrap()), "1");
        assert_eq!(iter.size_hint(), (3, Some(3)));
        assert_eq!(string_value(iter.next().unwrap().unwrap()), "two");
        assert_eq!(iter.size_hint(), (2, Some(2)));
        assert_eq!(iter.next().unwrap().unwrap(), JsonbItem::Boolean(true));
        assert_eq!(iter.size_hint(), (1, Some(1)));
        assert_eq!(iter.next().unwrap().unwrap(), JsonbItem::Null);
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn empty_array_iterator_reports_zero_remaining_items() {
        let jsonb = owned("[]");
        let mut iter = ArrayIterator::new(jsonb.as_raw()).unwrap().unwrap();

        assert_eq!(iter.len(), 0);
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn object_iterator_preserves_key_value_pairs_and_size_hint() {
        let jsonb = owned(r#"{"first":1,"second":"two","third":true}"#);
        let mut iter = ObjectIterator::new(jsonb.as_raw()).unwrap().unwrap();

        assert_eq!(iter.len(), 3);
        assert_eq!(iter.size_hint(), (3, Some(3)));

        let (key, value) = iter.next().unwrap().unwrap();
        assert_eq!(key, "first");
        assert_eq!(number_string(value), "1");
        assert_eq!(iter.size_hint(), (2, Some(2)));

        let (key, value) = iter.next().unwrap().unwrap();
        assert_eq!(key, "second");
        assert_eq!(string_value(value), "two");
        assert_eq!(iter.size_hint(), (1, Some(1)));

        let (key, value) = iter.next().unwrap().unwrap();
        assert_eq!(key, "third");
        assert_eq!(value, JsonbItem::Boolean(true));
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn empty_object_iterator_reports_zero_remaining_items() {
        let jsonb = owned("{}");
        let mut iter = ObjectIterator::new(jsonb.as_raw()).unwrap().unwrap();

        assert_eq!(iter.len(), 0);
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn object_key_and_value_iterators_report_exact_remaining_items() {
        let jsonb = owned(r#"{"first":1,"second":"two","third":true}"#);
        let mut keys = ObjectKeyIterator::new(jsonb.as_raw()).unwrap().unwrap();
        let mut values = ObjectValueIterator::new(jsonb.as_raw()).unwrap().unwrap();

        assert_eq!(keys.len(), 3);
        assert_eq!(keys.size_hint(), (3, Some(3)));
        assert_eq!(string_value(keys.next().unwrap().unwrap()), "first");
        assert_eq!(keys.size_hint(), (2, Some(2)));
        assert_eq!(string_value(keys.next().unwrap().unwrap()), "second");
        assert_eq!(keys.size_hint(), (1, Some(1)));
        assert_eq!(string_value(keys.next().unwrap().unwrap()), "third");
        assert_eq!(keys.size_hint(), (0, Some(0)));
        assert!(keys.next().is_none());

        assert_eq!(values.len(), 3);
        assert_eq!(values.size_hint(), (3, Some(3)));
        assert_eq!(number_string(values.next().unwrap().unwrap()), "1");
        assert_eq!(values.size_hint(), (2, Some(2)));
        assert_eq!(string_value(values.next().unwrap().unwrap()), "two");
        assert_eq!(values.size_hint(), (1, Some(1)));
        assert_eq!(values.next().unwrap().unwrap(), JsonbItem::Boolean(true));
        assert_eq!(values.size_hint(), (0, Some(0)));
        assert!(values.next().is_none());
    }

    /// `[<invalid UTF-8 string>, null]`.
    fn bad_first_element() -> Vec<u8> {
        let mut bytes: Vec<u8> = [0x8000_0002_u32, 0x1000_0001, 0x0000_0000]
            .iter()
            .flat_map(|w| w.to_be_bytes())
            .collect();
        bytes.push(0xff);
        bytes
    }

    #[test]
    fn nth_keeps_the_standard_semantics() {
        // `nth(1)` is `next()` twice: the first returns the error and stops
        // the iterator, so the second returns `None`.
        let bytes = bad_first_element();
        let mut iter = ArrayIterator::new(RawJsonb::new(&bytes)).unwrap().unwrap();
        assert!(iter.nth(1).is_none());
        let mut iter = ArrayIterator::new(RawJsonb::new(&bytes)).unwrap().unwrap();
        assert!(iter.next().unwrap().is_err());
        assert!(iter.next().is_none());
    }

    #[test]
    fn get_reports_errors_in_skipped_elements() {
        let bytes = bad_first_element();
        let iter = || ArrayIterator::new(RawJsonb::new(&bytes)).unwrap().unwrap();
        assert_eq!(iter().get(0).err(), Some(crate::Error::InvalidUtf8));
        assert_eq!(iter().get(1).err(), Some(crate::Error::InvalidUtf8));
        assert_eq!(iter().get(2), Ok(None));
        assert_eq!(iter().get(usize::MAX), Ok(None));

        let valid = owned("[1,true]");
        let iter = || ArrayIterator::new(valid.as_raw()).unwrap().unwrap();
        assert_eq!(iter().get(1), Ok(Some(JsonbItem::Boolean(true))));
        assert_eq!(number_string(iter().get(0).unwrap().unwrap()), "1");
    }
}
