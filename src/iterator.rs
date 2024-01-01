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

use std::{collections::VecDeque, str::from_utf8_unchecked};

use crate::{constants::CONTAINER_HEADER_LEN_MASK, jentry::JEntry, Error};

pub(crate) fn iterate_array(value: &[u8], header: u32) -> ArrayIterator<'_> {
    let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
    ArrayIterator {
        value,
        jentry_offset: 4,
        val_offset: 4 * length + 4,
        length,
        idx: 0,
    }
}

pub(crate) fn iteate_object_keys(value: &[u8], header: u32) -> ObjectKeyIterator<'_> {
    let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
    ObjectKeyIterator {
        value,
        jentry_offset: 4,
        key_offset: 8 * length + 4,
        length,
        idx: 0,
    }
}

pub(crate) fn iterate_object_entries(value: &[u8], header: u32) -> ObjectEntryIterator<'_> {
    let length = (header & CONTAINER_HEADER_LEN_MASK) as usize;
    ObjectEntryIterator {
        value,
        jentry_offset: 4,
        key_offset: 4 + length * 8,
        val_offset: 4 + length * 8,
        length,
        keys: None,
    }
}

pub(crate) struct ArrayIterator<'a> {
    value: &'a [u8],
    jentry_offset: usize,
    val_offset: usize,
    length: usize,
    idx: usize,
}

impl<'a> Iterator for ArrayIterator<'a> {
    type Item = (JEntry, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.length {
            return None;
        }
        let encoded = read_u32(self.value, self.jentry_offset).unwrap();
        let jentry = JEntry::decode_jentry(encoded);
        let val_length = jentry.length as usize;

        let item = (
            jentry,
            &self.value[self.val_offset..self.val_offset + val_length],
        );

        self.idx += 1;
        self.val_offset += val_length;
        self.jentry_offset += 4;

        Some(item)
    }
}

pub(crate) struct ObjectKeyIterator<'a> {
    value: &'a [u8],
    jentry_offset: usize,
    key_offset: usize,
    length: usize,
    idx: usize,
}

impl<'a> Iterator for ObjectKeyIterator<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.length {
            return None;
        }

        let encoded = read_u32(self.value, self.jentry_offset).unwrap();
        let jentry = JEntry::decode_jentry(encoded);
        let key_length = jentry.length as usize;

        let key = unsafe {
            from_utf8_unchecked(&self.value[self.key_offset..self.key_offset + key_length])
        };

        self.idx += 1;
        self.key_offset += key_length;
        self.jentry_offset += 4;

        Some(key)
    }
}

pub(crate) struct ObjectEntryIterator<'a> {
    value: &'a [u8],
    jentry_offset: usize,
    key_offset: usize,
    val_offset: usize,
    length: usize,
    keys: Option<VecDeque<JEntry>>,
}

impl<'a> Iterator for ObjectEntryIterator<'a> {
    type Item = (&'a str, JEntry, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.keys.is_none() {
            self.fill_keys();
        }
        match self.keys.as_mut().unwrap().pop_front() {
            Some(key_jentry) => {
                let prev_key_offset = self.key_offset;
                self.key_offset += key_jentry.length as usize;

                let key = unsafe {
                    std::str::from_utf8_unchecked(&self.value[prev_key_offset..self.key_offset])
                };

                let val_encoded = read_u32(self.value, self.jentry_offset).unwrap();
                let val_jentry = JEntry::decode_jentry(val_encoded);
                let val_length = val_jentry.length as usize;

                let val =
                    &self.value[self.val_offset..self.val_offset + val_jentry.length as usize];
                let result = (key, val_jentry, val);

                self.jentry_offset += 4;
                self.val_offset += val_length;

                Some(result)
            }
            None => None,
        }
    }
}

impl<'a> ObjectEntryIterator<'a> {
    fn fill_keys(&mut self) {
        let mut keys: VecDeque<JEntry> = VecDeque::with_capacity(self.length);
        for _ in 0..self.length {
            let encoded = read_u32(self.value, self.jentry_offset).unwrap();
            let key_jentry = JEntry::decode_jentry(encoded);

            self.jentry_offset += 4;
            self.val_offset += key_jentry.length as usize;
            keys.push_back(key_jentry);
        }
        self.keys = Some(keys);
    }
}

fn read_u32(buf: &[u8], idx: usize) -> Result<u32, Error> {
    let bytes: [u8; 4] = buf
        .get(idx..idx + 4)
        .ok_or(Error::InvalidEOF)?
        .try_into()
        .unwrap();
    Ok(u32::from_be_bytes(bytes))
}
