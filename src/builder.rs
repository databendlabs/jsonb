// Copyright 2024 Datafuse Labs.
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

use std::collections::BTreeMap;

use byteorder::{BigEndian, WriteBytesExt};

use crate::{
    constants::{ARRAY_CONTAINER_TAG, OBJECT_CONTAINER_TAG},
    jentry::JEntry,
};

enum Entry<'a> {
    ArrayBuilder(ArrayBuilder<'a>),
    ObjectBuilder(ObjectBuilder<'a>),
    Raw(JEntry, &'a [u8]),
}

pub(crate) struct ArrayBuilder<'a> {
    entries: Vec<Entry<'a>>,
}

impl<'a> ArrayBuilder<'a> {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
        }
    }

    pub(crate) fn push_raw(&mut self, jentry: JEntry, data: &'a [u8]) {
        self.entries.push(Entry::Raw(jentry, data));
    }

    pub(crate) fn push_array(&mut self, builder: ArrayBuilder<'a>) {
        self.entries.push(Entry::ArrayBuilder(builder));
    }

    pub(crate) fn push_object(&mut self, builder: ObjectBuilder<'a>) {
        self.entries.push(Entry::ObjectBuilder(builder));
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn build_into(self, buf: &mut Vec<u8>) {
        let header = ARRAY_CONTAINER_TAG | self.entries.len() as u32;
        buf.write_u32::<BigEndian>(header).unwrap();

        let mut jentry_index = reserve_jentries(buf, self.entries.len() * 4);

        for entry in self.entries.into_iter() {
            let jentry = write_entry(buf, entry);
            replace_jentry(buf, jentry, &mut jentry_index);
        }
    }
}

pub(crate) struct ObjectBuilder<'a> {
    entries: BTreeMap<&'a str, Entry<'a>>,
}

impl<'a> ObjectBuilder<'a> {
    pub(crate) fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    pub(crate) fn push_raw(&mut self, key: &'a str, jentry: JEntry, data: &'a [u8]) {
        self.entries.insert(key, Entry::Raw(jentry, data));
    }

    pub(crate) fn push_array(&mut self, key: &'a str, builder: ArrayBuilder<'a>) {
        self.entries.insert(key, Entry::ArrayBuilder(builder));
    }

    pub(crate) fn push_object(&mut self, key: &'a str, builder: ObjectBuilder<'a>) {
        self.entries.insert(key, Entry::ObjectBuilder(builder));
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn build_into(self, buf: &mut Vec<u8>) {
        let header = OBJECT_CONTAINER_TAG | self.entries.len() as u32;
        buf.write_u32::<BigEndian>(header).unwrap();

        let mut jentry_index = reserve_jentries(buf, self.entries.len() * 8);

        for (key, _) in self.entries.iter() {
            let key_len = key.len();
            buf.extend_from_slice(key.as_bytes());
            let jentry = JEntry::make_string_jentry(key_len);
            replace_jentry(buf, jentry, &mut jentry_index)
        }

        for (_, entry) in self.entries.into_iter() {
            let jentry = write_entry(buf, entry);
            replace_jentry(buf, jentry, &mut jentry_index);
        }
    }
}

fn write_entry(buf: &mut Vec<u8>, entry: Entry<'_>) -> JEntry {
    match entry {
        Entry::ArrayBuilder(builder) => {
            let jentry = JEntry::make_container_jentry(builder.len());
            builder.build_into(buf);
            jentry
        }
        Entry::ObjectBuilder(builder) => {
            let jentry = JEntry::make_container_jentry(builder.len());
            builder.build_into(buf);
            jentry
        }
        Entry::Raw(jentry, data) => {
            buf.extend_from_slice(data);
            jentry
        }
    }
}

fn reserve_jentries(buf: &mut Vec<u8>, len: usize) -> usize {
    let old_len = buf.len();
    let new_len = old_len + len;
    buf.resize(new_len, 0);
    old_len
}

fn replace_jentry(buf: &mut [u8], jentry: JEntry, jentry_index: &mut usize) {
    let jentry_bytes = jentry.encoded().to_be_bytes();
    for (i, b) in jentry_bytes.iter().enumerate() {
        buf[*jentry_index + i] = *b;
    }
    *jentry_index += 4;
}
