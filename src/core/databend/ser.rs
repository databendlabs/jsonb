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

use byteorder::BigEndian;
use byteorder::WriteBytesExt;
use serde::ser;
use serde::ser::Serialize;
use serde::ser::SerializeMap;
use serde::ser::SerializeSeq;

use super::constants::*;
use super::jentry::JEntry;
use crate::core::ArrayBuilder;
use crate::core::ObjectBuilder;
use crate::error::*;
use crate::extension::ExtensionValue;
use crate::number::Number;
use crate::value::Object;
use crate::value::Value;
use crate::Error;
use crate::OwnedJsonb;
use crate::RawJsonb;

/// `Serializer` is a custom serializer for JSONB data, implementing the
/// `serde::ser::Serializer` trait. It allows serializing Rust data structures
/// into a `Vec<u8>` representing the JSONB data.
#[derive(Debug, Default)]
pub struct Serializer {
    buffer: Vec<u8>,
}

impl Serializer {
    /// Creates a new `Serializer` with an empty buffer.
    pub fn new() -> Serializer {
        Serializer { buffer: Vec::new() }
    }

    /// Consumes the `Serializer` and returns the underlying buffer containing the
    /// serialized JSONB data.
    ///
    /// This function returns the `OwnedJsonb` that has been populated with the
    /// serialized JSONB data during the serialization process. The `Serializer`
    /// is consumed in the process.
    pub fn to_owned_jsonb(self) -> OwnedJsonb {
        OwnedJsonb::new(self.buffer)
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
    keys: Vec<String>,
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
        let raw_jsonb = key_jsonb.as_raw();
        let Ok(Some(key)) = raw_jsonb.as_str() else {
            return Err(ser::Error::custom("Invalid object key".to_string()));
        };
        self.keys.push(key.to_string());

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
            return Err(ser::Error::custom(
                "Invalid object keys and values length".to_string(),
            ));
        }
        let mut builder = ObjectBuilder::new();
        for (key_str, value) in self.keys.iter().zip(self.values.into_iter()) {
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
        let (header_type, header_len) = self
            .read_header(index)
            .map_err(|e| ser::Error::custom(format!("{e}")))?;
        index += 4;

        match header_type {
            SCALAR_CONTAINER_TAG => {
                let jentry = self
                    .read_jentry(index)
                    .map_err(|e| ser::Error::custom(format!("{e}")))?;
                index += 4;

                let payload_start = index;
                let payload_end = index + jentry.length as usize;
                match jentry.type_code {
                    NULL_TAG => serializer.serialize_unit(),
                    TRUE_TAG => serializer.serialize_bool(true),
                    FALSE_TAG => serializer.serialize_bool(false),
                    NUMBER_TAG => {
                        let num = Number::decode(&self.data[payload_start..payload_end])
                            .map_err(|e| ser::Error::custom(format!("{e}")))?;
                        num.serialize(serializer)
                    }
                    STRING_TAG => {
                        let s = unsafe {
                            std::str::from_utf8_unchecked(&self.data[payload_start..payload_end])
                        };
                        serializer.serialize_str(s)
                    }
                    EXTENSION_TAG => {
                        let val = ExtensionValue::decode(&self.data[payload_start..payload_end])
                            .map_err(|e| ser::Error::custom(format!("{e}")))?;
                        let s = format!("{}", val);
                        serializer.serialize_str(&s)
                    }
                    CONTAINER_TAG => {
                        // Scalar header can't have contianer jentry tag
                        Err(ser::Error::custom("Invalid jsonb".to_string()))
                    }
                    _ => Err(ser::Error::custom("Invalid jsonb".to_string())),
                }
            }
            ARRAY_CONTAINER_TAG => {
                let mut serialize_seq = serializer.serialize_seq(Some(header_len as usize))?;

                let mut payload_start = index + 4 * header_len as usize;
                for _ in 0..header_len {
                    let jentry = self
                        .read_jentry(index)
                        .map_err(|e| ser::Error::custom(format!("{e}")))?;
                    index += 4;

                    let payload_end = payload_start + jentry.length as usize;
                    match jentry.type_code {
                        NULL_TAG => serialize_seq.serialize_element(&())?,
                        TRUE_TAG => serialize_seq.serialize_element(&true)?,
                        FALSE_TAG => serialize_seq.serialize_element(&false)?,
                        NUMBER_TAG => {
                            let num = Number::decode(&self.data[payload_start..payload_end])
                                .map_err(|e| ser::Error::custom(format!("{e}")))?;
                            serialize_seq.serialize_element(&num)?;
                        }
                        STRING_TAG => {
                            let s = unsafe {
                                std::str::from_utf8_unchecked(
                                    &self.data[payload_start..payload_end],
                                )
                            };
                            serialize_seq.serialize_element(&s)?;
                        }
                        EXTENSION_TAG => {
                            let val =
                                ExtensionValue::decode(&self.data[payload_start..payload_end])
                                    .map_err(|e| ser::Error::custom(format!("{e}")))?;
                            let s = format!("{}", val);
                            serialize_seq.serialize_element(&s)?;
                        }
                        CONTAINER_TAG => {
                            let inner_raw_jsonb =
                                RawJsonb::new(&self.data[payload_start..payload_end]);
                            serialize_seq.serialize_element(&inner_raw_jsonb)?;
                        }
                        _ => {
                            return Err(ser::Error::custom("Invalid jsonb".to_string()));
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
                    let jentry = self
                        .read_jentry(index)
                        .map_err(|e| ser::Error::custom(format!("{e}")))?;
                    index += 4;

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
                            return Err(ser::Error::custom("Invalid jsonb".to_string()));
                        }
                    }
                    payload_start = payload_end;
                }

                for _ in 0..header_len {
                    let jentry = self
                        .read_jentry(index)
                        .map_err(|e| ser::Error::custom(format!("{e}")))?;
                    index += 4;

                    let payload_end = payload_start + jentry.length as usize;
                    let k = keys.pop_front().unwrap();
                    match jentry.type_code {
                        NULL_TAG => serialize_map.serialize_entry(&k, &())?,
                        TRUE_TAG => serialize_map.serialize_entry(&k, &true)?,
                        FALSE_TAG => serialize_map.serialize_entry(&k, &false)?,
                        NUMBER_TAG => {
                            let num = Number::decode(&self.data[payload_start..payload_end])
                                .map_err(|e| ser::Error::custom(format!("{e}")))?;
                            serialize_map.serialize_entry(&k, &num)?;
                        }
                        STRING_TAG => {
                            let s = unsafe {
                                std::str::from_utf8_unchecked(
                                    &self.data[payload_start..payload_end],
                                )
                            };
                            serialize_map.serialize_entry(&k, &s)?;
                        }
                        EXTENSION_TAG => {
                            let val =
                                ExtensionValue::decode(&self.data[payload_start..payload_end])
                                    .map_err(|e| ser::Error::custom(format!("{e}")))?;
                            let s = format!("{}", val);
                            serialize_map.serialize_entry(&k, &s)?;
                        }
                        CONTAINER_TAG => {
                            let inner_raw_jsonb =
                                RawJsonb::new(&self.data[payload_start..payload_end]);
                            serialize_map.serialize_entry(&k, &inner_raw_jsonb)?;
                        }
                        _ => {
                            return Err(ser::Error::custom("Invalid jsonb".to_string()));
                        }
                    }
                    payload_start = payload_end;
                }
                serialize_map.end()
            }
            _ => Err(ser::Error::custom("Invalid jsonb".to_string())),
        }
    }
}

pub(crate) struct Encoder<'a> {
    pub buf: &'a mut Vec<u8>,
}

impl<'a> Encoder<'a> {
    pub(crate) fn new(buf: &'a mut Vec<u8>) -> Encoder<'a> {
        Self { buf }
    }

    // Encode `JSONB` Value to a sequence of bytes
    pub(crate) fn encode(&mut self, value: &Value<'a>) {
        match value {
            Value::Array(array) => self.encode_array(array),
            Value::Object(obj) => self.encode_object(obj),
            _ => self.encode_scalar(value),
        };
    }

    // Encoded `Scalar` consists of a `Header`, a `JEntry` and encoded data
    fn encode_scalar(&mut self, value: &Value<'a>) -> usize {
        self.buf
            .write_u32::<BigEndian>(SCALAR_CONTAINER_TAG)
            .unwrap();

        // Scalar Value only has one JEntry
        let mut scalar_len = 4 + 4;
        let mut jentry_index = self.reserve_jentries(4);

        let jentry = self.encode_value(value);
        scalar_len += jentry.length as usize;
        self.replace_jentry(jentry, &mut jentry_index);

        scalar_len
    }

    // Encoded `Array` consists of a `Header`, N `JEntries` and encoded data
    // N is the number of `Array` inner values
    fn encode_array(&mut self, values: &[Value<'a>]) -> usize {
        let header = ARRAY_CONTAINER_TAG | values.len() as u32;
        self.buf.write_u32::<BigEndian>(header).unwrap();

        // `Array` has N `JEntries`
        let mut array_len = 4 + values.len() * 4;
        let mut jentry_index = self.reserve_jentries(values.len() * 4);

        // encode all values
        for value in values.iter() {
            let jentry = self.encode_value(value);
            array_len += jentry.length as usize;
            self.replace_jentry(jentry, &mut jentry_index);
        }

        array_len
    }

    // Encoded `Object` consists of a `Header`, 2 * N `JEntries` and encoded data
    // N is the number of `Object` inner key value pair
    fn encode_object(&mut self, obj: &Object<'a>) -> usize {
        let header = OBJECT_CONTAINER_TAG | obj.len() as u32;
        self.buf.write_u32::<BigEndian>(header).unwrap();

        // `Object` has 2 * N `JEntries`
        let mut object_len = 4 + obj.len() * 8;
        let mut jentry_index = self.reserve_jentries(obj.len() * 8);

        // encode all keys first
        for (key, _) in obj.iter() {
            let len = key.len();
            object_len += len;
            self.buf.extend_from_slice(key.as_bytes());
            let jentry = JEntry::make_string_jentry(len);
            self.replace_jentry(jentry, &mut jentry_index);
        }
        // encode all values
        for (_, value) in obj.iter() {
            let jentry = self.encode_value(value);
            object_len += jentry.length as usize;
            self.replace_jentry(jentry, &mut jentry_index);
        }

        object_len
    }

    // Reserve space for `JEntries` and fill them later
    // As the length of each `Value` cannot be known until the `Value` encoded
    fn reserve_jentries(&mut self, len: usize) -> usize {
        let old_len = self.buf.len();
        let new_len = old_len + len;
        self.buf.resize(new_len, 0);
        old_len
    }

    // Write encoded `JEntry` to the corresponding index
    fn replace_jentry(&mut self, jentry: JEntry, jentry_index: &mut usize) {
        let jentry_bytes = jentry.encoded().to_be_bytes();
        for (i, b) in jentry_bytes.iter().enumerate() {
            self.buf[*jentry_index + i] = *b;
        }
        *jentry_index += 4;
    }

    // `Null` and `Boolean` only has a `JEntry`
    // `Number` and `String` has a `JEntry` and an encoded data
    // `Array` and `Object` has a container `JEntry` and nested encoded data
    fn encode_value(&mut self, value: &Value<'a>) -> JEntry {
        let jentry = match value {
            Value::Null => JEntry::make_null_jentry(),
            Value::Bool(v) => {
                if *v {
                    JEntry::make_true_jentry()
                } else {
                    JEntry::make_false_jentry()
                }
            }
            Value::Number(v) => {
                let old_off = self.buf.len();
                let _ = v.compact_encode(&mut self.buf).unwrap();
                let len = self.buf.len() - old_off;
                JEntry::make_number_jentry(len)
            }
            Value::String(s) => {
                let len = s.len();
                self.buf.extend_from_slice(s.as_ref().as_bytes());
                JEntry::make_string_jentry(len)
            }
            Value::Binary(v) => {
                let old_off = self.buf.len();
                let val = ExtensionValue::Binary(v);
                let _ = val.compact_encode(&mut self.buf).unwrap();
                let len = self.buf.len() - old_off;
                JEntry::make_extension_jentry(len)
            }
            Value::Date(v) => {
                let old_off = self.buf.len();
                let val = ExtensionValue::Date(v.clone());
                let _ = val.compact_encode(&mut self.buf).unwrap();
                let len = self.buf.len() - old_off;
                JEntry::make_extension_jentry(len)
            }
            Value::Timestamp(v) => {
                let old_off = self.buf.len();
                let val = ExtensionValue::Timestamp(v.clone());
                let _ = val.compact_encode(&mut self.buf).unwrap();
                let len = self.buf.len() - old_off;
                JEntry::make_extension_jentry(len)
            }
            Value::TimestampTz(v) => {
                let old_off = self.buf.len();
                let val = ExtensionValue::TimestampTz(v.clone());
                let _ = val.compact_encode(&mut self.buf).unwrap();
                let len = self.buf.len() - old_off;
                JEntry::make_extension_jentry(len)
            }
            Value::Interval(v) => {
                let old_off = self.buf.len();
                let val = ExtensionValue::Interval(v.clone());
                let _ = val.compact_encode(&mut self.buf).unwrap();
                let len = self.buf.len() - old_off;
                JEntry::make_extension_jentry(len)
            }
            Value::Array(array) => {
                let len = self.encode_array(array);
                JEntry::make_container_jentry(len)
            }
            Value::Object(obj) => {
                let len = self.encode_object(obj);
                JEntry::make_container_jentry(len)
            }
        };

        jentry
    }
}
