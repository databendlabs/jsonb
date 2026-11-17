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

use std::collections::btree_map::Entry;
use std::collections::BTreeMap;

use super::constants::*;
use super::jentry::encode_container_header;
use super::jentry::JEntry;
use crate::core::ExtensionItem;
use crate::core::JsonbItem;
use crate::core::NumberItem;
use crate::core::RawEntry;
use crate::error::Error;
use crate::error::Result;
use crate::OwnedJsonb;
use crate::RawJsonb;

pub(crate) struct ArrayBuilder<'a> {
    items: Vec<JsonbItem<'a>>,
}

impl<'a> ArrayBuilder<'a> {
    pub(crate) fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            items: Vec::with_capacity(capacity),
        }
    }

    pub(crate) fn push_jsonb_item(&mut self, item: JsonbItem<'a>) {
        self.items.push(item);
    }

    pub(crate) fn push_raw_jsonb(&mut self, raw: RawJsonb<'a>) {
        self.push_jsonb_item(JsonbItem::Raw(raw));
    }

    pub(crate) fn push_owned_jsonb(&mut self, owned: OwnedJsonb) {
        self.push_jsonb_item(JsonbItem::Owned(owned));
    }

    pub(crate) fn build(self) -> Result<OwnedJsonb> {
        let mut writer = ContainerWriter::new(ARRAY_CONTAINER_TAG, self.items.len())?;
        for item in self.items {
            writer.push_item(item)?;
        }
        Ok(writer.finish())
    }
}

pub(crate) struct ArrayDistinctBuilder<'a> {
    items: Vec<JsonbItem<'a>>,
    item_map: BTreeMap<JsonbItem<'a>, usize>,
}

impl<'a> ArrayDistinctBuilder<'a> {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            items: Vec::with_capacity(capacity),
            item_map: BTreeMap::new(),
        }
    }

    pub(crate) fn push_jsonb_item(&mut self, item: JsonbItem<'a>) {
        if let Some(cnt) = self.item_map.get_mut(&item) {
            *cnt += 1;
        } else {
            self.item_map.insert(item.clone(), 1);
            self.items.push(item);
        }
    }

    pub(crate) fn pop_jsonb_item(&mut self, item: JsonbItem<'a>) -> Option<()> {
        if let Some(cnt) = self.item_map.get_mut(&item) {
            if *cnt > 0 {
                *cnt -= 1;
                return Some(());
            }
        }
        None
    }

    /// Builds an array of the distinct items, in the order first pushed.
    pub(crate) fn build(self) -> Result<OwnedJsonb> {
        ArrayBuilder { items: self.items }.build()
    }
}

pub(crate) struct ObjectBuilder<'a> {
    entries: BTreeMap<&'a str, JsonbItem<'a>>,
}

impl<'a> ObjectBuilder<'a> {
    pub(crate) fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    pub(crate) fn push_jsonb_item(&mut self, key: &'a str, val_item: JsonbItem<'a>) -> Result<()> {
        match self.entries.entry(key) {
            Entry::Vacant(entry) => {
                entry.insert(val_item);
                Ok(())
            }
            Entry::Occupied(_) => Err(Error::ObjectDuplicateKey),
        }
    }

    pub(crate) fn push_raw_jsonb(&mut self, key: &'a str, raw: RawJsonb<'a>) -> Result<()> {
        self.push_jsonb_item(key, JsonbItem::Raw(raw))
    }

    pub(crate) fn push_owned_jsonb(&mut self, key: &'a str, owned: OwnedJsonb) -> Result<()> {
        self.push_jsonb_item(key, JsonbItem::Owned(owned))
    }

    pub(crate) fn contains_key(&self, key: &'a str) -> bool {
        self.entries.contains_key(key)
    }

    pub(crate) fn build(self) -> Result<OwnedJsonb> {
        let mut writer = ContainerWriter::new(OBJECT_CONTAINER_TAG, self.entries.len())?;
        for key in self.entries.keys() {
            writer.push_key(key)?;
        }
        for item in self.entries.into_values() {
            writer.push_item(item)?;
        }
        Ok(writer.finish())
    }

    pub(crate) fn build_from_entries(
        mut entries: Vec<(String, JsonbItem<'a>)>,
    ) -> Result<OwnedJsonb> {
        entries.sort_by(|(left, _), (right, _)| left.cmp(right));
        if entries.windows(2).any(|entry| entry[0].0 == entry[1].0) {
            return Err(Error::ObjectDuplicateKey);
        }
        let mut writer = ContainerWriter::new(OBJECT_CONTAINER_TAG, entries.len())?;
        for (key, _) in &entries {
            writer.push_key(key)?;
        }
        for (_, item) in entries {
            writer.push_item(item)?;
        }
        Ok(writer.finish())
    }
}

impl OwnedJsonb {
    /// Encodes `item` as a JSONB value of its own.
    pub(crate) fn from_item(item: JsonbItem<'_>) -> Result<OwnedJsonb> {
        let payload_len = match item {
            JsonbItem::Raw(raw_jsonb) => return Ok(raw_jsonb.to_owned()),
            JsonbItem::Owned(owned_jsonb) => return Ok(owned_jsonb),
            JsonbItem::Null | JsonbItem::Boolean(_) => 0,
            JsonbItem::Number(NumberItem::Raw(data)) => data.len(),
            JsonbItem::String(ref s) => s.len(),
            JsonbItem::Extension(ExtensionItem::Raw(data)) => data.len(),
            // An estimate for decoded numbers and extension values.
            _ => 10,
        };
        let mut writer = ContainerWriter::scalar(payload_len);
        writer.push_item(item)?;
        Ok(writer.finish())
    }
}

/// Writes JSONB: a header, the `JEntries`, then their payloads. Each member
/// fills the next reserved `JEntry` and appends its payload.
struct ContainerWriter {
    buf: Vec<u8>,
    /// Where the next `JEntry` goes.
    jentry_index: usize,
}

impl ContainerWriter {
    /// Starts an array or object of `len` members. An object has a key and a
    /// value `JEntry` for each member.
    ///
    /// # Errors
    ///
    /// Returns `Error::ValueTooLarge` if `len` does not fit the header.
    fn new(container_tag: u32, len: usize) -> Result<Self> {
        let header = encode_container_header(container_tag, len)?;
        let jentries = if container_tag == OBJECT_CONTAINER_TAG {
            2 * len
        } else {
            len
        };
        Ok(Self::with_header(header, jentries, 0))
    }

    /// Starts a scalar, a single `JEntry` under the scalar header, with room
    /// for `payload_len` payload bytes.
    fn scalar(payload_len: usize) -> Self {
        Self::with_header(SCALAR_CONTAINER_TAG, 1, payload_len)
    }

    fn with_header(header: u32, jentries: usize, payload_len: usize) -> Self {
        let jentries_end = 4 + 4 * jentries;
        let mut buf = Vec::with_capacity(jentries_end + payload_len);
        buf.extend_from_slice(&header.to_be_bytes());
        buf.resize(jentries_end, 0);
        Self {
            buf,
            jentry_index: 4,
        }
    }

    fn finish(self) -> OwnedJsonb {
        OwnedJsonb::new(self.buf)
    }

    fn set_jentry(&mut self, jentry: JEntry) {
        jentry.write_at(&mut self.buf, &mut self.jentry_index);
    }

    fn push_key(&mut self, key: &str) -> Result<()> {
        self.set_jentry(JEntry::make_string_jentry(key.len())?);
        self.buf.extend_from_slice(key.as_bytes());
        Ok(())
    }

    fn push_item(&mut self, item: JsonbItem) -> Result<()> {
        let jentry = match item {
            JsonbItem::Null => JEntry::make_null_jentry(),
            JsonbItem::Boolean(true) => JEntry::make_true_jentry(),
            JsonbItem::Boolean(false) => JEntry::make_false_jentry(),
            JsonbItem::Number(NumberItem::Raw(data)) => {
                self.buf.extend_from_slice(data);
                JEntry::make_number_jentry(data.len())?
            }
            JsonbItem::Number(NumberItem::Number(num)) => {
                JEntry::make_number_jentry(num.compact_encode(&mut self.buf)?)?
            }
            JsonbItem::String(data) => {
                // Check the length before copying a possibly huge payload.
                let jentry = JEntry::make_string_jentry(data.len())?;
                self.buf.extend_from_slice(data.as_bytes());
                jentry
            }
            JsonbItem::Extension(ExtensionItem::Raw(data)) => {
                self.buf.extend_from_slice(data);
                JEntry::make_extension_jentry(data.len())?
            }
            JsonbItem::Extension(ExtensionItem::Extension(ext)) => {
                JEntry::make_extension_jentry(ext.compact_encode(&mut self.buf)?)?
            }
            JsonbItem::Raw(raw_jsonb) => return self.push_raw(raw_jsonb),
            JsonbItem::Owned(owned_jsonb) => return self.push_raw(owned_jsonb.as_raw()),
        };
        self.set_jentry(jentry);
        Ok(())
    }

    /// Appends a JSONB value as a member: a container as a container entry,
    /// and a scalar as an entry with its `JEntry` and payload.
    ///
    /// Copying everything after a scalar's `JEntry` used to copy bytes past
    /// its payload too, which shifted the payloads of the members after it.
    /// `from_jsonb` rejects a container entry under a scalar header and a
    /// truncated payload.
    fn push_raw(&mut self, raw_jsonb: RawJsonb) -> Result<()> {
        let entry = RawEntry::from_jsonb(raw_jsonb)?;
        let jentry = if entry.is_container() {
            JEntry::make_container_jentry(entry.payload.len())?
        } else {
            JEntry {
                type_code: entry.type_code,
                // `from_jsonb` read the payload by this length, so it fits.
                length: entry.payload.len() as u32,
            }
        };
        self.set_jentry(jentry);
        self.buf.extend_from_slice(entry.payload);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::ArrayBuilder;
    use super::ObjectBuilder;
    use crate::to_owned_jsonb;
    use crate::Value;

    #[test]
    fn test_build_with_inner_array() {
        let from_builder = {
            let mut builder = ObjectBuilder::new();
            let mut inner_array_builder = ArrayBuilder::with_capacity(1);

            let val = to_owned_jsonb(&false).unwrap();
            inner_array_builder.push_owned_jsonb(val);
            let array = inner_array_builder.build().unwrap();

            builder.push_owned_jsonb("arr", array).unwrap();
            let object = builder.build().unwrap();
            object.to_vec()
        };
        let mut from_encoder = Vec::new();
        {
            let value = init_object(vec![("arr", Value::Array(vec![Value::Bool(false)]))]);
            value.write_to_vec(&mut from_encoder).unwrap();
        }
        assert_eq!(from_builder, from_encoder);
    }

    #[test]
    fn test_build_with_inner_object() {
        let from_builder = {
            let mut builder = ObjectBuilder::new();
            let mut inner_obj_builder = ObjectBuilder::new();

            let val = to_owned_jsonb(&true).unwrap();
            inner_obj_builder.push_owned_jsonb("field", val).unwrap();
            let inner_obj = inner_obj_builder.build().unwrap();

            builder.push_owned_jsonb("obj", inner_obj).unwrap();
            let object = builder.build().unwrap();
            object.to_vec()
        };
        let mut from_encoder = Vec::new();
        {
            let value = init_object(vec![(
                "obj",
                init_object(vec![("field", Value::Bool(true))]),
            )]);
            value.write_to_vec(&mut from_encoder).unwrap();
        }
        assert_eq!(from_builder, from_encoder);
    }

    fn init_object<'a>(entries: Vec<(&str, Value<'a>)>) -> Value<'a> {
        let mut map = BTreeMap::new();
        for (key, val) in entries {
            map.insert(key.to_string(), val);
        }
        Value::Object(map)
    }
}
