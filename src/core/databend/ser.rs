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

use std::collections::VecDeque;

use crate::constants::*;
use crate::core::ArrayBuilder;
use crate::core::ObjectBuilder;
use crate::error::*;
use crate::from_raw_jsonb;
use crate::jentry::JEntry;
use crate::number::Number;
use crate::Error;
use crate::OwnedJsonb;
use crate::RawJsonb;

use serde::ser::Error as SerError;
use serde::ser::SerializeMap;
use serde::ser::SerializeSeq;

use serde::ser::{self, Serialize};

use byteorder::BigEndian;
use byteorder::WriteBytesExt;

#[derive(Debug, Default)]
pub struct Serializer {
    buffer: Vec<u8>,
}

impl Serializer {
    fn new() -> Serializer {
        Serializer { buffer: Vec::new() }
    }

    fn write_jentry(&mut self, jentry: JEntry) -> Result<()> {
        self.buffer.write_u32::<BigEndian>(SCALAR_CONTAINER_TAG)?;
        let jentry_bytes = jentry.encoded();
        self.buffer.write_u32::<BigEndian>(jentry_bytes)?;
        Ok(())
    }

    fn replace_jentry(&mut self, jentry: JEntry, jentry_index: &mut usize) {
        let jentry_bytes = jentry.encoded().to_be_bytes();
        for (i, b) in jentry_bytes.iter().enumerate() {
            self.buffer[*jentry_index + i] = *b;
        }
        *jentry_index += 4;
    }

    fn write_number(&mut self, v: Number) -> Result<()> {
        self.buffer.write_u32::<BigEndian>(SCALAR_CONTAINER_TAG)?;
        let mut jentry_index = self.buffer.len();
        let payload_index = jentry_index + 4;
        // resize buffer to keep space for jentry.
        self.buffer.resize(payload_index, 0);

        let _ = v.compact_encode(&mut self.buffer)?;
        let len = self.buffer.len() - payload_index;
        let jentry = JEntry::make_number_jentry(len);

        self.replace_jentry(jentry, &mut jentry_index);
        Ok(())
    }

    fn write_str(&mut self, s: &str) -> Result<()> {
        self.buffer.write_u32::<BigEndian>(SCALAR_CONTAINER_TAG)?;
        let mut jentry_index = self.buffer.len();
        let payload_index = jentry_index + 4;
        // resize buffer to keep space for jentry.
        self.buffer.resize(payload_index, 0);

        let len = s.len();
        self.buffer.extend_from_slice(s.as_bytes());
        let jentry = JEntry::make_string_jentry(len);

        self.replace_jentry(jentry, &mut jentry_index);
        Ok(())
    }

    pub fn to_vec(self) -> Vec<u8> {
        self.buffer
    }
}

/// Serialize a value into a JSONB byte array
pub fn to_owned_jsonb<T>(value: &T) -> Result<OwnedJsonb>
where
    T: Serialize,
{
    let mut serializer = Serializer::default();
    value.serialize(&mut serializer)?;
    Ok(OwnedJsonb::new(serializer.buffer))
}

/// Serialize a value into a JSONB byte array
pub fn to_vec2<T>(value: &T) -> Result<Vec<u8>>
where
    T: Serialize,
{
    let mut serializer = Serializer::default();
    value.serialize(&mut serializer)?;
    Ok(serializer.buffer)
}

impl<'a> ser::Serializer for &'a mut Serializer {
    type Ok = ();

    type Error = Error;

    type SerializeSeq = ArraySerializer<'a>;

    type SerializeTuple = ArraySerializer<'a>;

    type SerializeTupleStruct = ArraySerializer<'a>;

    type SerializeTupleVariant = ArraySerializer<'a>;

    type SerializeMap = ObjectSerializer<'a>;

    type SerializeStruct = ObjectSerializer<'a>;

    type SerializeStructVariant = ArraySerializer<'a>;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok> {
        let jentry = if v {
            JEntry::make_true_jentry()
        } else {
            JEntry::make_false_jentry()
        };
        self.write_jentry(jentry)
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok> {
        self.write_number(Number::Int64(v as i64))
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok> {
        self.write_number(Number::Int64(v as i64))
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok> {
        self.write_number(Number::Int64(v as i64))
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok> {
        self.write_number(Number::Int64(v))
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok> {
        self.write_number(Number::UInt64(v as u64))
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok> {
        self.write_number(Number::UInt64(v as u64))
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok> {
        self.write_number(Number::UInt64(v as u64))
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok> {
        self.write_number(Number::UInt64(v))
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok> {
        self.write_number(Number::Float64(v as f64))
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok> {
        self.write_number(Number::Float64(v))
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok> {
        let s: String = v.to_string();
        self.write_str(s.as_str())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok> {
        self.write_str(v)
    }

    fn serialize_bytes(self, _v: &[u8]) -> Result<Self::Ok> {
        todo!()
    }

    fn serialize_none(self) -> Result<Self::Ok> {
        self.serialize_unit()
    }

    fn serialize_some<T: ?Sized + Serialize>(self, value: &T) -> Result<Self::Ok> {
        T::serialize(value, self)
    }

    fn serialize_unit(self) -> Result<Self::Ok> {
        let jentry = JEntry::make_null_jentry();
        self.write_jentry(jentry)
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok> {
        self.serialize_unit()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        _value: &T,
    ) -> Result<Self::Ok> {
        self.serialize_unit()
    }

    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<Self::Ok> {
        todo!()
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq> {
        Ok(ArraySerializer::new(&mut self.buffer, len))
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        todo!()
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        todo!()
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap> {
        Ok(ObjectSerializer::new(&mut self.buffer, len))
    }

    fn serialize_struct(self, _name: &'static str, len: usize) -> Result<Self::SerializeStruct> {
        self.serialize_map(Some(len))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        todo!()
    }
}

pub struct ArraySerializer<'a> {
    buffer: &'a mut Vec<u8>,
    items: Vec<OwnedJsonb>,
}

impl<'a> ArraySerializer<'a> {
    pub fn new(buffer: &'a mut Vec<u8>, len: Option<usize>) -> Self {
        let len = len.unwrap_or_default();
        let items = Vec::with_capacity(len);

        Self { buffer, items }
    }
}

impl ser::SerializeSeq for ArraySerializer<'_> {
    type Ok = ();

    type Error = Error;

    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<()> {
        let mut serializer = Serializer::new();
        let res = value.serialize(&mut serializer);
        let item_jsonb = OwnedJsonb::new(serializer.buffer);
        self.items.push(item_jsonb);
        res
    }

    fn end(self) -> Result<Self::Ok> {
        let mut builder = ArrayBuilder::with_capacity(self.items.len());
        for item in self.items.into_iter() {
            builder.push_owned_jsonb(item);
        }
        let array_jsonb = builder.build()?;
        let mut buf = array_jsonb.to_vec();
        self.buffer.append(&mut buf);
        Ok(())
    }
}

impl ser::SerializeTuple for ArraySerializer<'_> {
    type Ok = ();

    type Error = Error;

    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<()> {
        <Self as ser::SerializeSeq>::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok> {
        <Self as ser::SerializeSeq>::end(self)
    }
}

pub struct ObjectSerializer<'a> {
    buffer: &'a mut Vec<u8>,
    keys: Vec<OwnedJsonb>,
    values: Vec<OwnedJsonb>,
}

impl<'a> ObjectSerializer<'a> {
    fn new(buffer: &'a mut Vec<u8>, len: Option<usize>) -> Self {
        let len = len.unwrap_or_default();
        let keys = Vec::with_capacity(len);
        let values = Vec::with_capacity(len);

        Self {
            buffer,
            keys,
            values,
        }
    }
}

impl ser::SerializeMap for ObjectSerializer<'_> {
    type Ok = ();

    type Error = Error;

    fn serialize_key<T: ?Sized + Serialize>(&mut self, key: &T) -> Result<()> {
        let mut serializer = Serializer::new();
        let res = key.serialize(&mut serializer);
        let key_jsonb = OwnedJsonb::new(serializer.buffer);
        self.keys.push(key_jsonb);

        res
    }

    fn serialize_value<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<()> {
        let mut serializer = Serializer::new();
        let res = value.serialize(&mut serializer);
        let value_jsonb = OwnedJsonb::new(serializer.buffer);
        self.values.push(value_jsonb);

        res
    }

    fn end(self) -> Result<Self::Ok> {
        if self.keys.len() != self.values.len() {
            return Err(SerError::custom(
                "Invalid object keys and values length".to_string(),
            ));
        }
        let mut key_strs = Vec::with_capacity(self.keys.len());
        for key in self.keys.into_iter() {
            let key_str_res: Result<String> = from_raw_jsonb(&key.as_raw());
            let Ok(key_str) = key_str_res else {
                return Err(SerError::custom("Invalid object key".to_string()));
            };
            key_strs.push(key_str);
        }
        let mut builder = ObjectBuilder::new();
        for (key_str, value) in key_strs.iter().zip(self.values.into_iter()) {
            builder.push_owned_jsonb(key_str, value)?;
        }
        let object_jsonb = builder.build()?;
        let mut buf = object_jsonb.to_vec();
        self.buffer.append(&mut buf);
        Ok(())
    }
}

impl ser::SerializeStruct for ObjectSerializer<'_> {
    type Ok = ();

    type Error = Error;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<()> {
        <Self as ser::SerializeMap>::serialize_key(self, key)?;
        <Self as ser::SerializeMap>::serialize_value(self, value)
    }

    fn end(self) -> Result<Self::Ok> {
        Ok(())
    }
}

impl ser::SerializeTupleStruct for ArraySerializer<'_> {
    type Ok = ();

    type Error = Error;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        _value: &T,
    ) -> std::prelude::v1::Result<(), Self::Error> {
        todo!()
    }

    fn end(self) -> Result<Self::Ok> {
        todo!()
    }
}

impl ser::SerializeTupleVariant for ArraySerializer<'_> {
    type Ok = ();

    type Error = Error;

    fn serialize_field<T: ?Sized + Serialize>(&mut self, _value: &T) -> Result<()> {
        todo!()
    }

    fn end(self) -> Result<Self::Ok> {
        todo!()
    }
}

impl ser::SerializeStructVariant for ArraySerializer<'_> {
    type Ok = ();

    type Error = Error;

    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        _key: &'static str,
        _value: &T,
    ) -> Result<()> {
        todo!()
    }

    fn end(self) -> Result<Self::Ok> {
        todo!()
    }
}

impl Serialize for RawJsonb<'_> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> core::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut index = 0;
        let header = self
            .read_u32(index)
            .map_err(|e| SerError::custom(format!("{e}")))?;
        index += 4;
        let header_type = header & CONTAINER_HEADER_TYPE_MASK;
        let header_len = header & CONTAINER_HEADER_LEN_MASK;

        match header_type {
            SCALAR_CONTAINER_TAG => {
                let jentry_encoded = self
                    .read_u32(index)
                    .map_err(|e| SerError::custom(format!("{e}")))?;
                index += 4;
                let jentry = JEntry::decode_jentry(jentry_encoded);

                match jentry.type_code {
                    NULL_TAG => serializer.serialize_unit(),
                    TRUE_TAG => serializer.serialize_bool(true),
                    FALSE_TAG => serializer.serialize_bool(false),
                    NUMBER_TAG => {
                        let payload_start = index;
                        let payload_end = index + jentry.length as usize;

                        let num = Number::decode(&self.data[payload_start..payload_end])
                            .map_err(|e| SerError::custom(format!("{e}")))?;

                        match num {
                            Number::Int64(i) => serializer.serialize_i64(i),
                            Number::UInt64(i) => serializer.serialize_u64(i),
                            Number::Float64(i) => serializer.serialize_f64(i),
                        }
                    }
                    STRING_TAG => {
                        let payload_start = index;
                        let payload_end = index + jentry.length as usize;

                        let s = unsafe {
                            std::str::from_utf8_unchecked(&self.data[payload_start..payload_end])
                        };
                        serializer.serialize_str(s)
                    }
                    CONTAINER_TAG => {
                        // Scalar header can't have contianer jentry tag
                        Err(SerError::custom("Invalid jsonb".to_string()))
                    }
                    _ => Err(SerError::custom("Invalid jsonb".to_string())),
                }
            }
            ARRAY_CONTAINER_TAG => {
                let mut serialize_seq = serializer.serialize_seq(Some(header_len as usize))?;

                let mut payload_start = index + 4 * header_len as usize;
                for _ in 0..header_len {
                    let jentry_encoded = self
                        .read_u32(index)
                        .map_err(|e| SerError::custom(format!("{e}")))?;
                    index += 4;
                    let jentry = JEntry::decode_jentry(jentry_encoded);

                    let payload_end = payload_start + jentry.length as usize;
                    match jentry.type_code {
                        NULL_TAG => serialize_seq.serialize_element(&())?,
                        TRUE_TAG => serialize_seq.serialize_element(&true)?,
                        FALSE_TAG => serialize_seq.serialize_element(&false)?,
                        NUMBER_TAG => {
                            let num = Number::decode(&self.data[payload_start..payload_end])
                                .map_err(|e| SerError::custom(format!("{e}")))?;
                            match num {
                                Number::Int64(i) => serialize_seq.serialize_element(&i)?,
                                Number::UInt64(i) => serialize_seq.serialize_element(&i)?,
                                Number::Float64(i) => serialize_seq.serialize_element(&i)?,
                            }
                        }
                        STRING_TAG => {
                            let s = unsafe {
                                std::str::from_utf8_unchecked(
                                    &self.data[payload_start..payload_end],
                                )
                            };
                            serialize_seq.serialize_element(&s)?;
                        }
                        CONTAINER_TAG => {
                            let inner_raw_jsonb =
                                RawJsonb::new(&self.data[payload_start..payload_end]);
                            serialize_seq.serialize_element(&inner_raw_jsonb)?;
                        }
                        _ => {
                            return Err(SerError::custom("Invalid jsonb".to_string()));
                        }
                    }
                    payload_start = payload_end;
                }
                serialize_seq.end()
            }
            OBJECT_CONTAINER_TAG => {
                let mut serialize_map = serializer.serialize_map(Some(header_len as usize))?;

                let mut keys = VecDeque::with_capacity(header_len as usize);
                let mut payload_start = index + 8 * header_len as usize;
                for _ in 0..header_len {
                    let jentry_encoded = self
                        .read_u32(index)
                        .map_err(|e| SerError::custom(format!("{e}")))?;
                    index += 4;
                    let jentry = JEntry::decode_jentry(jentry_encoded);

                    let payload_end = payload_start + jentry.length as usize;
                    match jentry.type_code {
                        STRING_TAG => {
                            let s = unsafe {
                                std::str::from_utf8_unchecked(
                                    &self.data[payload_start..payload_end],
                                )
                            };
                            keys.push_back(s);
                        }
                        _ => {
                            return Err(SerError::custom("Invalid jsonb".to_string()));
                        }
                    }
                    payload_start = payload_end;
                }

                for _ in 0..header_len {
                    let jentry_encoded = self
                        .read_u32(index)
                        .map_err(|e| SerError::custom(format!("{e}")))?;
                    index += 4;
                    let jentry = JEntry::decode_jentry(jentry_encoded);

                    let payload_end = payload_start + jentry.length as usize;
                    let k = keys.pop_front().unwrap();
                    match jentry.type_code {
                        NULL_TAG => serialize_map.serialize_entry(&k, &())?,
                        TRUE_TAG => serialize_map.serialize_entry(&k, &true)?,
                        FALSE_TAG => serialize_map.serialize_entry(&k, &false)?,
                        NUMBER_TAG => {
                            let num = Number::decode(&self.data[payload_start..payload_end])
                                .map_err(|e| SerError::custom(format!("{e}")))?;
                            match num {
                                Number::Int64(i) => serialize_map.serialize_entry(&k, &i)?,
                                Number::UInt64(i) => serialize_map.serialize_entry(&k, &i)?,
                                Number::Float64(i) => serialize_map.serialize_entry(&k, &i)?,
                            }
                        }
                        STRING_TAG => {
                            let s = unsafe {
                                std::str::from_utf8_unchecked(
                                    &self.data[payload_start..payload_end],
                                )
                            };
                            serialize_map.serialize_entry(&k, &s)?;
                        }
                        CONTAINER_TAG => {
                            let inner_raw_jsonb =
                                RawJsonb::new(&self.data[payload_start..payload_end]);
                            serialize_map.serialize_entry(&k, &inner_raw_jsonb)?;
                        }
                        _ => {
                            return Err(SerError::custom("Invalid jsonb".to_string()));
                        }
                    }
                    payload_start = payload_end;
                }
                serialize_map.end()
            }
            _ => Err(SerError::custom("Invalid jsonb".to_string())),
        }
    }
}
