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

use std::borrow::Cow;
use std::collections::VecDeque;
use std::convert::TryFrom;

use ethnum::i256;
use num_traits::FromPrimitive;
use serde::de;
use serde::de::Deserialize;
use serde::de::IntoDeserializer;
use serde::de::Visitor;

use super::constants::*;
use super::jentry::JEntry;
use super::util::decode_str;
use crate::constants::enter_container;
use crate::error::Error;
use crate::error::Result;
use crate::extension::ExtensionValue;
use crate::number::Number;
use crate::RawJsonb;

/// `Deserializer` is a custom deserializer for JSONB data, implementing the
/// `serde::de::Deserializer` trait. It allows deserializing a `RawJsonb` into
/// Rust data structures using Serde.
pub struct Deserializer<'de> {
    index: usize,
    current_jentry: Option<JEntry>,
    raw: &'de RawJsonb<'de>,
    /// The offset just past the member being read, or the end of the data
    /// at the top level. Reads stop there, so that a member cannot read the
    /// members after it.
    member_end: usize,
    /// Number of arrays and objects currently being deserialized
    depth: usize,
}

impl<'de> Deserializer<'de> {
    /// Creates a new `Deserializer` from a `RawJsonb`.
    ///
    /// This function initializes the deserializer with the provided `RawJsonb` data.
    ///
    /// # Arguments
    ///
    /// * `raw_jsonb`: A reference to the `RawJsonb` containing the JSONB data to deserialize.
    pub fn new(raw_jsonb: &'de RawJsonb) -> Self {
        Self {
            index: 0,
            current_jentry: None,
            raw: raw_jsonb,
            member_end: raw_jsonb.len(),
            depth: 0,
        }
    }

    /// Checks if the deserializer has reached the end of the `RawJsonb` data.
    ///
    /// This function returns `true` if the current index is equal to the length of
    /// the `RawJsonb` data, indicating that all data has been processed.
    pub fn end(&self) -> bool {
        self.index == self.raw.len()
    }

    /// Runs `f` one array or object level deeper.
    ///
    /// # Errors
    ///
    /// Returns `Error::RecursionLimitExceeded` past the nesting limit, or the
    /// error returned by `f`.
    fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        self.depth = enter_container(self.depth)?;
        let result = f(self);
        self.depth -= 1;
        result
    }

    /// Checks that `len` bytes at the current position lie within the member
    /// being read.
    #[inline]
    fn check_within(&self, len: usize) -> Result<()> {
        match self.index.checked_add(len) {
            Some(end) if end <= self.member_end => Ok(()),
            _ => Err(Error::InvalidEOF),
        }
    }

    fn read_header(&mut self) -> Result<(u32, usize)> {
        let header = self.raw.read_header(self.index)?;
        self.index += 4;
        Ok(header)
    }

    fn read_jentry(&mut self) -> Result<JEntry> {
        let jentry = self.raw.read_jentry(self.index)?;
        self.index += 4;
        Ok(jentry)
    }

    fn set_jentry(&mut self, jentry: JEntry) {
        self.current_jentry = Some(jentry);
    }

    fn set_jentry_with_index(&mut self, jentry: JEntry, index: usize) {
        self.current_jentry = Some(jentry);
        self.index = index;
    }

    /// Deserializes the member described by `jentry`, whose payload starts at
    /// `start`, with `f`, reading nothing past its payload.
    ///
    /// Bounds checks used to cover the whole document, so a nested container
    /// whose `JEntry` length was too short read the next member's bytes as
    /// its own: `[<array of one string, without the string>, "x"]` read as
    /// `[["x"], "x"]`, where `to_value` fails.
    fn read_member<T>(
        &mut self,
        jentry: JEntry,
        start: usize,
        f: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        // A scalar reads exactly its `JEntry` length of payload, so only a
        // container needs its end recorded.
        if jentry.type_code != CONTAINER_TAG {
            self.set_jentry_with_index(jentry, start);
            return f(self);
        }
        let end = match start.checked_add(jentry.length as usize) {
            Some(end) if end <= self.member_end => end,
            _ => return Err(Error::InvalidEOF),
        };
        let parent = std::mem::replace(&mut self.member_end, end);
        self.set_jentry_with_index(jentry, start);
        let result = f(self);
        self.member_end = parent;
        result
    }

    /// Takes the `JEntry` of the scalar to deserialize: the current member's,
    /// or at the top level the one under the scalar header.
    fn read_scalar_jentry(&mut self) -> Result<JEntry> {
        if let Some(jentry) = self.current_jentry.take() {
            return Ok(jentry);
        }
        let (header_type, _) = self.read_header()?;
        match header_type {
            SCALAR_CONTAINER_TAG => {
                let jentry = self.read_jentry()?;
                // A scalar header never holds a container entry; see
                // `RawJsonb::value_with_depth`.
                if jentry.type_code == CONTAINER_TAG {
                    return Err(Error::InvalidJsonb);
                }
                Ok(jentry)
            }
            // An array or object; `read_header` rejects unknown header types.
            _ => Err(Error::UnexpectedType),
        }
    }

    /// Reads the header of the value to deserialize as an array or object: a
    /// container member's, or the top-level one. A scalar member, or a
    /// scalar at the top level, gives `SCALAR_CONTAINER_TAG`.
    ///
    /// A member is positioned at its payload, which used to be read as a
    /// header whatever the member's type, so the string `"@\0\0\0"` read
    /// as an empty object.
    fn read_container_header(&mut self) -> Result<(u32, usize)> {
        let jentry = match self.current_jentry.take() {
            Some(jentry) if jentry.type_code == CONTAINER_TAG => return self.read_header(),
            Some(jentry) => jentry,
            None => {
                let header = self.read_header()?;
                if header.0 != SCALAR_CONTAINER_TAG {
                    return Ok(header);
                }
                self.raw.read_jentry(self.index)?
            }
        };
        match jentry.type_code {
            NULL_TAG | TRUE_TAG | FALSE_TAG | NUMBER_TAG | STRING_TAG | EXTENSION_TAG => {
                Ok((SCALAR_CONTAINER_TAG, 0))
            }
            // A container under a scalar header, or an unknown type.
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Returns the offset just past the payloads of `jentries`, which start
    /// at `start`.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidEOF` if the payloads extend past the data,
    /// including lengths whose sum overflows on 32-bit targets.
    fn payloads_end<'j>(
        &self,
        start: usize,
        jentries: impl IntoIterator<Item = &'j JEntry>,
    ) -> Result<usize> {
        let mut end = start;
        for jentry in jentries {
            end = end
                .checked_add(jentry.length as usize)
                .ok_or(Error::InvalidEOF)?;
        }
        if end > self.member_end {
            return Err(Error::InvalidEOF);
        }
        Ok(end)
    }

    /// Deserializes the array of `len` members whose header was just read,
    /// one nesting level deeper, and moves past it.
    ///
    /// # Errors
    ///
    /// Fails if `visitor` stops before the last member, as serde_json does. A
    /// tuple used to stop early and leave the position inside the array, so
    /// the next value was read at the wrong offset.
    // Not inlined: inlined into `deserialize_any`, it slowed the scalar path
    // that most members take.
    #[inline(never)]
    fn visit_array<V>(&mut self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let jentries = self.read_jentries(len)?;
        let start = self.index;
        let end = self.payloads_end(start, &jentries)?;
        let value = self.nested(|de| {
            let mut seq = ArrayDeserializer::new(de, jentries, start);
            let value = visitor.visit_seq(&mut seq)?;
            if !seq.jentries.is_empty() {
                return Err(de::Error::invalid_length(len, &"fewer elements in array"));
            }
            Ok(value)
        })?;
        self.index = end;
        Ok(value)
    }

    /// Deserializes the object of `len` members whose header was just read,
    /// one nesting level deeper, and moves past it.
    ///
    /// # Errors
    ///
    /// Fails if `visitor` stops before reading the last value, as for arrays.
    fn visit_object<V>(&mut self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let key_jentries = self.read_jentries(len)?;
        let value_jentries = self.read_jentries(len)?;
        let keys_start = self.index;
        let values_start = self.payloads_end(keys_start, &key_jentries)?;
        let end = self.payloads_end(values_start, &value_jentries)?;
        let value = self.nested(|de| {
            let mut map =
                ObjectDeserializer::new(de, keys_start, key_jentries, values_start, value_jentries);
            let value = visitor.visit_map(&mut map)?;
            // A visitor that stopped early used to succeed, and the members
            // it skipped were never checked.
            if !map.value_jentries.is_empty() {
                return Err(de::Error::invalid_length(len, &"fewer members in object"));
            }
            Ok(value)
        })?;
        self.index = end;
        Ok(value)
    }

    /// Reads the `count` consecutive `JEntries` at the current position.
    fn read_jentries(&mut self, count: usize) -> Result<VecDeque<JEntry>> {
        // One bound check for all of them, instead of one per `JEntry`.
        self.check_within(count.saturating_mul(4))?;
        let mut jentries = VecDeque::with_capacity(count);
        for _ in 0..count {
            jentries.push_back(self.raw.read_jentry(self.index)?);
            self.index += 4;
        }
        Ok(jentries)
    }

    /// Borrows `length` payload bytes at the current index and advances past them.
    fn read_payload(&mut self, length: usize) -> Result<&'de [u8]> {
        let start = self.index;
        let end = start.checked_add(length).ok_or(Error::InvalidEOF)?;
        if end > self.member_end {
            return Err(Error::InvalidEOF);
        }
        let data = self.raw.data.get(start..end).ok_or(Error::InvalidEOF)?;
        self.index = end;
        Ok(data)
    }

    fn read_payload_number(&mut self, length: usize) -> Result<Number> {
        Number::decode(self.read_payload(length)?)
    }

    fn read_payload_str(&mut self, length: usize) -> Result<&'de str> {
        decode_str(self.read_payload(length)?)
    }

    fn read_payload_extension(&mut self, length: usize) -> Result<ExtensionValue<'de>> {
        ExtensionValue::decode(self.read_payload(length)?)
    }

    fn read_null(&mut self) -> Result<()> {
        let jentry = self.read_scalar_jentry()?;
        match jentry.type_code {
            NULL_TAG => Ok(()),
            FALSE_TAG | TRUE_TAG | NUMBER_TAG | STRING_TAG | CONTAINER_TAG | EXTENSION_TAG => {
                Err(Error::UnexpectedType)
            }
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn read_bool(&mut self) -> Result<bool> {
        let jentry = self.read_scalar_jentry()?;
        match jentry.type_code {
            FALSE_TAG => Ok(false),
            TRUE_TAG => Ok(true),
            NULL_TAG | NUMBER_TAG | STRING_TAG | CONTAINER_TAG | EXTENSION_TAG => {
                Err(Error::UnexpectedType)
            }
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn read_number(&mut self) -> Result<Number> {
        let jentry = self.read_scalar_jentry()?;
        match jentry.type_code {
            NUMBER_TAG => {
                let length = jentry.length as usize;
                let num = self.read_payload_number(length)?;
                Ok(num)
            }
            NULL_TAG | FALSE_TAG | TRUE_TAG | STRING_TAG | CONTAINER_TAG | EXTENSION_TAG => {
                Err(Error::UnexpectedType)
            }
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn read_integer<T>(&mut self) -> Result<T>
    where
        for<'a> T: Deserialize<'a> + FromPrimitive,
    {
        let num = self.read_number()?;
        match num {
            Number::Int64(n) => T::from_i64(n).ok_or(Error::UnexpectedType),
            Number::UInt64(n) => T::from_u64(n).ok_or(Error::UnexpectedType),
            Number::Float64(_)
            | Number::Decimal64(_)
            | Number::Decimal128(_)
            | Number::Decimal256(_) => Err(Error::UnexpectedType),
        }
    }

    /// Reads an integer for `deserialize_i128` and `deserialize_u128`: an
    /// `Int64`, a `UInt64`, or a decimal with scale 0, which is how
    /// `serialize_i128` and `serialize_u128` write larger values.
    fn read_wide_integer(&mut self) -> Result<i256> {
        match self.read_number()? {
            Number::Int64(n) => Ok(n.into()),
            Number::UInt64(n) => Ok(n.into()),
            Number::Decimal64(d) if d.scale == 0 => Ok(d.value.into()),
            Number::Decimal128(d) if d.scale == 0 => Ok(d.value.into()),
            Number::Decimal256(d) if d.scale == 0 => Ok(d.value),
            _ => Err(Error::UnexpectedType),
        }
    }

    fn read_float<T>(&mut self) -> Result<T>
    where
        for<'a> T: Deserialize<'a> + FromPrimitive,
    {
        match self.read_number()? {
            Number::Int64(n) => T::from_i64(n),
            Number::UInt64(n) => T::from_u64(n),
            num => T::from_f64(num.as_f64()),
        }
        .ok_or(Error::UnexpectedType)
    }

    /// Reads a string, borrowed from the data, or an extension value as text.
    fn read_str(&mut self) -> Result<Cow<'de, str>> {
        let jentry = self.read_scalar_jentry()?;
        match jentry.type_code {
            STRING_TAG => Ok(Cow::Borrowed(
                self.read_payload_str(jentry.length as usize)?,
            )),
            EXTENSION_TAG => {
                let val = self.read_payload_extension(jentry.length as usize)?;
                Ok(Cow::Owned(val.to_string()))
            }
            NULL_TAG | FALSE_TAG | TRUE_TAG | NUMBER_TAG | CONTAINER_TAG => {
                Err(Error::UnexpectedType)
            }
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn read_string(&mut self) -> Result<String> {
        Ok(self.read_str()?.into_owned())
    }

    /// Reads a value for `deserialize_bytes` and `deserialize_byte_buf`.
    ///
    /// A binary value gives its bytes, so values written by `serialize_bytes`
    /// read back unchanged, and a string gives its UTF-8 bytes, as in
    /// serde_json. Other extension values give their text, as for
    /// `deserialize_str`.
    fn read_bytes<V>(&mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let jentry = self.read_scalar_jentry()?;
        let length = jentry.length as usize;
        match jentry.type_code {
            STRING_TAG => {
                let s = decode_str(self.read_payload(length)?)?;
                visitor.visit_borrowed_bytes(s.as_bytes())
            }
            EXTENSION_TAG => match ExtensionValue::decode(self.read_payload(length)?)? {
                ExtensionValue::Binary(v) => visitor.visit_borrowed_bytes(v),
                value => visitor.visit_string(value.to_string()),
            },
            NULL_TAG | FALSE_TAG | TRUE_TAG | NUMBER_TAG | CONTAINER_TAG => {
                Err(Error::UnexpectedType)
            }
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn read_with_jentry<V>(&mut self, jentry: JEntry, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match jentry.type_code {
            NULL_TAG => visitor.visit_unit(),
            TRUE_TAG => visitor.visit_bool(true),
            FALSE_TAG => visitor.visit_bool(false),
            STRING_TAG => {
                visitor.visit_borrowed_str(self.read_payload_str(jentry.length as usize)?)
            }
            NUMBER_TAG => {
                let length = jentry.length as usize;
                let num = self.read_payload_number(length)?;
                match num {
                    Number::Int64(i) => {
                        if let Ok(x) = u8::try_from(i) {
                            visitor.visit_u8(x)
                        } else if let Ok(x) = i8::try_from(i) {
                            visitor.visit_i8(x)
                        } else if let Ok(x) = u16::try_from(i) {
                            visitor.visit_u16(x)
                        } else if let Ok(x) = i16::try_from(i) {
                            visitor.visit_i16(x)
                        } else if let Ok(x) = u32::try_from(i) {
                            visitor.visit_u32(x)
                        } else if let Ok(x) = i32::try_from(i) {
                            visitor.visit_i32(x)
                        } else if let Ok(x) = u64::try_from(i) {
                            visitor.visit_u64(x)
                        } else {
                            visitor.visit_i64(i)
                        }
                    }
                    Number::UInt64(i) => {
                        if let Ok(x) = u8::try_from(i) {
                            visitor.visit_u8(x)
                        } else if let Ok(x) = u16::try_from(i) {
                            visitor.visit_u16(x)
                        } else if let Ok(x) = u32::try_from(i) {
                            visitor.visit_u32(x)
                        } else {
                            visitor.visit_u64(i)
                        }
                    }
                    num => visitor.visit_f64(num.as_f64()),
                }
            }
            EXTENSION_TAG => {
                let val = self.read_payload_extension(jentry.length as usize)?;
                visitor.visit_string(val.to_string())
            }
            CONTAINER_TAG => Err(Error::UnexpectedType),
            _ => Err(Error::InvalidJsonb),
        }
    }
}

impl<'de> de::Deserializer<'de> for &mut Deserializer<'de> {
    type Error = Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.current_jentry.take() {
            Some(jentry) if jentry.type_code != CONTAINER_TAG => {
                return self.read_with_jentry(jentry, visitor);
            }
            // A container member, read at its payload, or the top level.
            _ => {}
        }
        let (header_type, header_len) = self.read_header()?;
        match header_type {
            SCALAR_CONTAINER_TAG => {
                let jentry = self.read_jentry()?;
                // `read_header` and `read_jentry` check only the document's
                // length. A container member holding just a scalar header
                // would read its `JEntry` from the next member, and a null or
                // boolean then reads no payload that would fail. Arrays and
                // objects check in `read_jentries`, and other scalar headers
                // are at the top level, which ends with the document.
                self.check_within(0)?;
                match jentry.type_code {
                    // A scalar header holds a single scalar, never a
                    // container; see `RawJsonb::value_with_depth`.
                    CONTAINER_TAG => Err(Error::InvalidJsonb),
                    _ => self.read_with_jentry(jentry, visitor),
                }
            }
            ARRAY_CONTAINER_TAG => self.visit_array(header_len, visitor),
            OBJECT_CONTAINER_TAG => self.visit_object(header_len, visitor),
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_bool(self.read_bool()?)
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i8(self.read_integer()?)
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i16(self.read_integer()?)
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i32(self.read_integer()?)
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i64(self.read_integer()?)
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_u8(self.read_integer()?)
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_u16(self.read_integer()?)
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_u32(self.read_integer()?)
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_u64(self.read_integer()?)
    }

    fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let value = self.read_wide_integer()?;
        visitor.visit_i128(i128::try_from(value).map_err(|_| Error::UnexpectedType)?)
    }

    fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let value = self.read_wide_integer()?;
        visitor.visit_u128(u128::try_from(value).map_err(|_| Error::UnexpectedType)?)
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_f32(self.read_float()?)
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_f64(self.read_float()?)
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        // A char is one Unicode scalar value, which takes up to 4 bytes.
        let s = self.read_str()?;
        let mut chars = s.chars();
        match (chars.next(), chars.next()) {
            (Some(c), None) => visitor.visit_char(c),
            _ => Err(Error::Message("invalid string length for char".into())),
        }
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.read_str()? {
            Cow::Borrowed(s) => visitor.visit_borrowed_str(s),
            Cow::Owned(s) => visitor.visit_string(s),
        }
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_string(self.read_string()?)
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.read_bytes(visitor)
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.read_bytes(visitor)
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let (index, jentry) = (self.index, self.current_jentry.clone());
        if self.read_null().is_ok() {
            visitor.visit_none()
        } else {
            self.index = index;
            self.current_jentry = jentry;
            visitor.visit_some(self)
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.read_null()?;
        visitor.visit_unit()
    }

    fn deserialize_unit_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }

    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.read_container_header()? {
            (ARRAY_CONTAINER_TAG, len) => self.visit_array(len, visitor),
            (SCALAR_CONTAINER_TAG | OBJECT_CONTAINER_TAG, _) => Err(Error::UnexpectedType),
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.read_container_header()? {
            (OBJECT_CONTAINER_TAG, len) => self.visit_object(len, visitor),
            (SCALAR_CONTAINER_TAG | ARRAY_CONTAINER_TAG, _) => Err(Error::UnexpectedType),
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_map(visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let (index, jentry) = (self.index, self.current_jentry.clone());
        match self.read_container_header()? {
            // A unit variant is its name, as `serialize_unit_variant` writes
            // it; only an object such as `{"Unit": null}` used to be read.
            (SCALAR_CONTAINER_TAG, _) => {
                self.index = index;
                self.current_jentry = jentry;
                // Only a string: `read_str` also gives an extension value's
                // text, so a date matched a variant renamed to its text.
                let jentry = self.read_scalar_jentry()?;
                if jentry.type_code != STRING_TAG {
                    return Err(Error::UnexpectedType);
                }
                let variant = self.read_payload_str(jentry.length as usize)?;
                visitor.visit_enum(variant.into_deserializer())
            }
            // Other variants are an object with one member.
            (OBJECT_CONTAINER_TAG, 1) => {
                let key_jentry = self.read_jentry()?;
                let value_jentry = self.read_jentry()?;
                if key_jentry.type_code != STRING_TAG {
                    return Err(Error::InvalidJsonb);
                }
                let value_start = self.payloads_end(self.index, [&key_jentry])?;
                let end = self.payloads_end(value_start, [&value_jentry])?;
                self.set_jentry(key_jentry);
                let key = self.read_string()?;
                let value = self.nested(|de| {
                    visitor.visit_enum(EnumDeserializer::new(de, key, value_jentry, value_start))
                })?;
                self.index = end;
                Ok(value)
            }
            (OBJECT_CONTAINER_TAG | ARRAY_CONTAINER_TAG, _) => Err(Error::UnexpectedType),
            _ => Err(Error::InvalidJsonb),
        }
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    /// Skips the current value, such as an object field the target type does
    /// not know.
    ///
    /// The value is read like any other, so it is checked the same way and
    /// counts toward the nesting limit. Skipping its bytes unread accepted
    /// invalid values, and at the top level any input, even an empty one.
    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }

    #[inline]
    fn is_human_readable(&self) -> bool {
        false
    }
}

/// Reads the members of an array, each at its payload, as
/// `ObjectDeserializer` reads values.
struct ArrayDeserializer<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
    jentries: VecDeque<JEntry>,
    payload_offset: usize,
}

impl<'a, 'de> ArrayDeserializer<'a, 'de> {
    fn new(
        de: &'a mut Deserializer<'de>,
        jentries: VecDeque<JEntry>,
        payload_offset: usize,
    ) -> Self {
        ArrayDeserializer {
            de,
            jentries,
            payload_offset,
        }
    }
}

impl<'de> de::SeqAccess<'de> for ArrayDeserializer<'_, 'de> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: de::DeserializeSeed<'de>,
    {
        let Some(jentry) = self.jentries.pop_front() else {
            return Ok(None);
        };
        // `visit_array` checked that the payloads fit in the data, so this
        // cannot overflow.
        let payload_offset = self.payload_offset;
        self.payload_offset += jentry.length as usize;
        self.de
            .read_member(jentry, payload_offset, |de| seed.deserialize(de))
            .map(Some)
    }

    /// The number of members not read yet; it used to stay at the array's
    /// length.
    #[inline]
    fn size_hint(&self) -> Option<usize> {
        Some(self.jentries.len())
    }
}

struct ObjectDeserializer<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
    key_jentries: VecDeque<JEntry>,
    key_payload_offset: usize,
    value_jentries: VecDeque<JEntry>,
    value_payload_offset: usize,
}

impl<'a, 'de> ObjectDeserializer<'a, 'de> {
    fn new(
        de: &'a mut Deserializer<'de>,
        key_payload_offset: usize,
        key_jentries: VecDeque<JEntry>,
        value_payload_offset: usize,
        value_jentries: VecDeque<JEntry>,
    ) -> Self {
        ObjectDeserializer {
            de,
            key_payload_offset,
            key_jentries,
            value_payload_offset,
            value_jentries,
        }
    }
}

impl<'de> de::MapAccess<'de> for ObjectDeserializer<'_, 'de> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: de::DeserializeSeed<'de>,
    {
        if let Some(jentry) = self.key_jentries.pop_front() {
            // A key used to be read as any type, so a map with integer keys
            // accepted a number key.
            if jentry.type_code != STRING_TAG {
                return Err(Error::InvalidJsonb);
            }
            let key_payload_offset = self.key_payload_offset;
            self.key_payload_offset += jentry.length as usize;
            self.de
                .read_member(jentry, key_payload_offset, |de| seed.deserialize(de))
                .map(Some)
        } else {
            Ok(None)
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: de::DeserializeSeed<'de>,
    {
        if let Some(jentry) = self.value_jentries.pop_front() {
            let value_payload_offset = self.value_payload_offset;
            self.value_payload_offset += jentry.length as usize;
            self.de
                .read_member(jentry, value_payload_offset, |de| seed.deserialize(de))
        } else {
            Err(Error::InvalidJsonb)
        }
    }

    /// The number of members whose key is not read yet.
    #[inline]
    fn size_hint(&self) -> Option<usize> {
        Some(self.key_jentries.len())
    }
}

struct EnumDeserializer<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
    key: String,
    jentry: JEntry,
    payload_offset: usize,
}

impl<'a, 'de> EnumDeserializer<'a, 'de> {
    fn new(
        de: &'a mut Deserializer<'de>,
        key: String,
        jentry: JEntry,
        payload_offset: usize,
    ) -> Self {
        EnumDeserializer {
            de,
            key,
            jentry,
            payload_offset,
        }
    }
}

impl<'de> de::EnumAccess<'de> for EnumDeserializer<'_, 'de> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: de::DeserializeSeed<'de>,
    {
        let key_variant = self.key.clone().into_deserializer();
        seed.deserialize(key_variant).map(|v| (v, self))
    }
}

impl<'de> de::VariantAccess<'de> for EnumDeserializer<'_, 'de> {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        self.de
            .read_member(self.jentry, self.payload_offset, |de| de.read_null())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: de::DeserializeSeed<'de>,
    {
        self.de
            .read_member(self.jentry, self.payload_offset, |de| seed.deserialize(de))
    }

    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.de.read_member(self.jentry, self.payload_offset, |de| {
            de::Deserializer::deserialize_seq(de, visitor)
        })
    }

    fn struct_variant<V>(self, _fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.de.read_member(self.jentry, self.payload_offset, |de| {
            de::Deserializer::deserialize_map(de, visitor)
        })
    }
}
