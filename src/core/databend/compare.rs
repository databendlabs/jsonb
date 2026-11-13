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

//! Ordering of undecoded JSONB values.
//!
//! Strings and object keys compare as bytes, without UTF-8 validation: UTF-8
//! orders byte-wise like the characters it encodes, so the ordering matches
//! `JsonbItem`'s.

use std::cmp::Ordering;

use crate::constants::enter_container;
use crate::core::Entries;
use crate::core::JsonbItemType;
use crate::core::RawEntry;
use crate::extension::ExtensionValue;
use crate::number::Number;

/// Compares two values by the JSONB ordering, where `depth` is the number of
/// containers enclosing them. Matches `JsonbItem`'s ordering.
///
/// Returns `None` for incomparable or invalid values, including containers
/// nested deeper than the recursion limit.
pub(crate) fn compare_entries(a: RawEntry<'_>, b: RawEntry<'_>, depth: usize) -> Option<Ordering> {
    let (a, b) = (a.unwrap_scalar().ok()?, b.unwrap_scalar().ok()?);
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
                let ord = compare_entries(a_item.ok()?, b_item.ok()?, depth)?;
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
                let ord = compare_entries(a_value.ok()?, b_value.ok()?, depth)?;
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
        compare_entries(self.0, other.0, 0).unwrap_or(Ordering::Equal)
    }
}
