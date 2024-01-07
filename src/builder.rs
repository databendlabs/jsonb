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

    pub(crate) fn build_into(self, buf: &mut Vec<u8>) -> usize {
        let header = ARRAY_CONTAINER_TAG | self.entries.len() as u32;
        buf.write_u32::<BigEndian>(header).unwrap();

        let mut array_len = 4 + self.entries.len() * 4;
        let mut jentry_index = reserve_jentries(buf, self.entries.len() * 4);

        for entry in self.entries.into_iter() {
            let jentry = write_entry(buf, entry);
            array_len += jentry.length as usize;
            replace_jentry(buf, jentry, &mut jentry_index);
        }
        array_len
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

    pub(crate) fn build_into(self, buf: &mut Vec<u8>) -> usize {
        let header = OBJECT_CONTAINER_TAG | self.entries.len() as u32;
        buf.write_u32::<BigEndian>(header).unwrap();

        let mut object_len = 4 + self.entries.len() * 8;
        let mut jentry_index = reserve_jentries(buf, self.entries.len() * 8);

        for (key, _) in self.entries.iter() {
            let key_len = key.len();
            object_len += key_len;
            buf.extend_from_slice(key.as_bytes());
            let jentry = JEntry::make_string_jentry(key_len);
            replace_jentry(buf, jentry, &mut jentry_index)
        }

        for (_, entry) in self.entries.into_iter() {
            let jentry = write_entry(buf, entry);
            object_len += jentry.length as usize;
            replace_jentry(buf, jentry, &mut jentry_index);
        }
        object_len
    }
}

fn write_entry(buf: &mut Vec<u8>, entry: Entry<'_>) -> JEntry {
    match entry {
        Entry::ArrayBuilder(builder) => {
            let size = builder.build_into(buf);
            JEntry::make_container_jentry(size)
        }
        Entry::ObjectBuilder(builder) => {
            let size = builder.build_into(buf);
            JEntry::make_container_jentry(size)
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{jentry::JEntry, Value};

    use super::{ArrayBuilder, ObjectBuilder};

    #[test]
    fn test_build_with_inner_array() {
        let mut from_builder = Vec::new();
        {
            let mut builder = ObjectBuilder::new();
            let mut inner_array_builder = ArrayBuilder::new(1);
            inner_array_builder.push_raw(JEntry::make_false_jentry(), &[]);

            builder.push_array("arr", inner_array_builder);
            builder.build_into(&mut from_builder);
        }
        let mut from_encoder = Vec::new();
        {
            let value = init_object(vec![("arr", Value::Array(vec![Value::Bool(false)]))]);
            value.write_to_vec(&mut from_encoder);
        }
        assert_eq!(from_builder, from_encoder);
    }

    #[test]
    fn test_build_with_inner_object() {
        let mut from_builder = Vec::new();
        {
            let mut builder = ObjectBuilder::new();
            let mut inner_obj_builder = ObjectBuilder::new();
            inner_obj_builder.push_raw("field", JEntry::make_true_jentry(), &[]);

            builder.push_object("obj", inner_obj_builder);
            builder.build_into(&mut from_builder);
        }
        let mut from_encoder = Vec::new();
        {
            let value = init_object(vec![(
                "obj",
                init_object(vec![("field", Value::Bool(true))]),
            )]);
            value.write_to_vec(&mut from_encoder);
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
