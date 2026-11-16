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

//! Iterators that decode the entries of JSONB containers into `JsonbItem`s,
//! validating strings as UTF-8. They read the entries with [`Entries`].

use std::iter::FusedIterator;

use super::constants::*;
use crate::core::Entries;
use crate::core::JsonbItem;
use crate::core::RawEntry;
use crate::error::Result;
use crate::RawJsonb;

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

            // `#[inline]` here, on `read_next` and on `RawEntry::into_item`
            // lets callers such as the JSONPath selector inline the decoding;
            // without it, `select_by_path` was up to 25% slower with
            // Databend's `opt-level = "s"` release profile.
            #[inline]
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

    #[inline]
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

    #[inline]
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

    #[inline]
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

    #[inline]
    fn read_next(&mut self) -> Option<Result<(&'a str, JsonbItem<'a>)>> {
        let key = self.keys.next()?.and_then(|key| key.object_key());
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
