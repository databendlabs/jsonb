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

//! Writes JSONB as JSON text without going through `serde::Serialize`.
//!
//! `Serialize` hands every string to the serializer as `&str`, so each string
//! must be validated as UTF-8 before it is escaped. This writer escapes the
//! string bytes directly and validates the whole output once at the end. One
//! long validation is much faster than many short ones, because SIMD
//! validation only pays off on long inputs.
//!
//! The output must match `Serialize` with serde_json's `CompactFormatter` or
//! `PrettyFormatter` byte for byte. The string escaping and the pretty layout
//! are copied from serde_json 1.0.154 (`src/ser.rs`,
//! <https://github.com/serde-rs/json>, licensed under MIT or Apache-2.0) and
//! adapted to write bytes into a `Vec<u8>`. Numbers are written by
//! `Number::write_json`, which mirrors serde_json's number formatting.

use super::constants::*;
use crate::constants::enter_container;
use crate::core::Entries;
use crate::core::RawEntry;
use crate::error::Error;
use crate::error::Result;
use crate::extension::ExtensionValue;
use crate::number::Number;
use crate::RawJsonb;

/// Writes JSONB as JSON text into a buffer it owns.
pub(crate) struct JsonWriter {
    buf: Vec<u8>,
    pretty: bool,
}

impl JsonWriter {
    /// Writes `raw` as JSON text, compact or pretty-printed.
    ///
    /// # Errors
    ///
    /// Returns an error if `raw` is not valid JSONB, or `Error::InvalidUtf8`
    /// if a string in it is not valid UTF-8.
    pub(crate) fn write(raw: RawJsonb<'_>, pretty: bool) -> Result<String> {
        let mut writer = Self {
            buf: Vec::with_capacity(raw.len()),
            pretty,
        };
        writer.write_raw(raw, 0)?;
        // Strings were copied without validation; check the whole output once.
        simdutf8::basic::from_utf8(&writer.buf).map_err(|_| Error::InvalidUtf8)?;
        // SAFETY: `buf` was validated as UTF-8 just above.
        Ok(unsafe { String::from_utf8_unchecked(writer.buf) })
    }

    /// Writes a JSONB value; `depth` is the number of containers enclosing it.
    fn write_raw(&mut self, raw: RawJsonb<'_>, depth: usize) -> Result<()> {
        let (header_type, header_len) = raw.read_header(0)?;
        match header_type {
            // `RawEntry::from_jsonb` rejects a container under a scalar header.
            SCALAR_CONTAINER_TAG => self.write_scalar(RawEntry::from_jsonb(raw)?),
            ARRAY_CONTAINER_TAG => {
                let inner = enter_container(depth)?;
                self.buf.push(b'[');
                for (i, item) in Entries::new(raw, header_len).enumerate() {
                    let item = item?;
                    self.begin_member(i, inner);
                    self.write_member(item, inner)?;
                }
                self.end_container(b']', header_len, depth);
                Ok(())
            }
            OBJECT_CONTAINER_TAG => {
                let inner = enter_container(depth)?;
                let (keys, values) = Entries::object(raw, header_len)?;
                self.buf.push(b'{');
                for (i, (key, value)) in keys.zip(values).enumerate() {
                    let key = key?;
                    if key.type_code != STRING_TAG {
                        return Err(Error::InvalidJsonb);
                    }
                    self.begin_member(i, inner);
                    self.write_str(key.payload);
                    let colon: &[u8] = if self.pretty { b": " } else { b":" };
                    self.buf.extend_from_slice(colon);
                    self.write_member(value?, inner)?;
                }
                self.end_container(b'}', header_len, depth);
                Ok(())
            }
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Writes a member of a container; `depth` is the number of containers
    /// enclosing it.
    fn write_member(&mut self, entry: RawEntry<'_>, depth: usize) -> Result<()> {
        if entry.is_container() {
            self.write_raw(entry.container(), depth)
        } else {
            self.write_scalar(entry)
        }
    }

    /// Writes a scalar entry.
    ///
    /// Kept out of line so that its locals do not enlarge the stack frame of
    /// the recursion through `write_raw`, which runs up to
    /// `MAX_NESTING_DEPTH` levels deep.
    #[inline(never)]
    fn write_scalar(&mut self, entry: RawEntry<'_>) -> Result<()> {
        let payload = entry.payload;
        match entry.type_code {
            NULL_TAG => self.buf.extend_from_slice(b"null"),
            TRUE_TAG => self.buf.extend_from_slice(b"true"),
            FALSE_TAG => self.buf.extend_from_slice(b"false"),
            NUMBER_TAG => Number::decode(payload)?.write_json(&mut self.buf)?,
            STRING_TAG => self.write_str(payload),
            EXTENSION_TAG => {
                let value = ExtensionValue::decode(payload)?;
                self.write_str(value.to_string().as_bytes());
            }
            _ => return Err(Error::InvalidJsonb),
        }
        Ok(())
    }

    // The container layout below follows serde_json's `CompactFormatter` and
    // `PrettyFormatter` (`begin_array_value`, `end_array` and their object
    // counterparts), with an indent of two spaces per enclosing container.

    /// Writes the separator before member `index` of a container whose
    /// members are enclosed by `depth` containers.
    fn begin_member(&mut self, index: usize, depth: usize) {
        if self.pretty {
            let separator: &[u8] = if index == 0 { b"\n" } else { b",\n" };
            self.buf.extend_from_slice(separator);
            self.write_indent(depth);
        } else if index > 0 {
            self.buf.push(b',');
        }
    }

    /// Closes a container of `len` members that is enclosed by `depth`
    /// containers. An empty container stays on one line.
    fn end_container(&mut self, close: u8, len: usize, depth: usize) {
        if self.pretty && len > 0 {
            self.buf.push(b'\n');
            self.write_indent(depth);
        }
        self.buf.push(close);
    }

    fn write_indent(&mut self, depth: usize) {
        for _ in 0..depth {
            self.buf.extend_from_slice(b"  ");
        }
    }

    /// Writes `bytes` as a quoted, escaped JSON string.
    ///
    /// Adapted from serde_json's `format_escaped_str` and
    /// `format_escaped_str_contents`: copy runs of bytes that need no escape,
    /// and write an escape sequence for each byte that does. Only ASCII
    /// bytes are escaped, so multi-byte UTF-8 sequences are copied intact.
    fn write_str(&mut self, bytes: &[u8]) {
        self.buf.push(b'"');
        let mut start = 0;
        for (i, &byte) in bytes.iter().enumerate() {
            let escape = ESCAPE[byte as usize];
            if escape == 0 {
                continue;
            }
            self.buf.extend_from_slice(&bytes[start..i]);
            write_char_escape(&mut self.buf, escape, byte);
            start = i + 1;
        }
        self.buf.extend_from_slice(&bytes[start..]);
        self.buf.push(b'"');
    }
}

/// Writes the escape sequence for `byte`, whose `ESCAPE` entry is `escape`.
///
/// Copied from serde_json's `Formatter::write_char_escape`. serde_json maps
/// the table entry to a `CharEscape` and back to the same character; this
/// writes the entry directly.
fn write_char_escape(buf: &mut Vec<u8>, escape: u8, byte: u8) {
    if escape == UU {
        static HEX_DIGITS: [u8; 16] = *b"0123456789abcdef";
        buf.extend_from_slice(&[
            b'\\',
            b'u',
            b'0',
            b'0',
            HEX_DIGITS[(byte >> 4) as usize],
            HEX_DIGITS[(byte & 0xF) as usize],
        ]);
    } else {
        buf.extend_from_slice(&[b'\\', escape]);
    }
}

// The escape table below is copied verbatim from serde_json.

const BB: u8 = b'b'; // \x08
const TT: u8 = b't'; // \x09
const NN: u8 = b'n'; // \x0A
const FF: u8 = b'f'; // \x0C
const RR: u8 = b'r'; // \x0D
const QU: u8 = b'"'; // \x22
const BS: u8 = b'\\'; // \x5C
const UU: u8 = b'u'; // \x00...\x1F except the ones above
const __: u8 = 0;

// Lookup table of escape sequences. A value of b'x' at index i means that byte
// i is escaped as "\x" in JSON. A value of 0 means that byte i is not escaped.
static ESCAPE: [u8; 256] = [
    //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
    UU, UU, UU, UU, UU, UU, UU, UU, BB, TT, NN, UU, FF, RR, UU, UU, // 0
    UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, // 1
    __, __, QU, __, __, __, __, __, __, __, __, __, __, __, __, __, // 2
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 3
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 4
    __, __, __, __, __, __, __, __, __, __, __, __, BS, __, __, __, // 5
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 6
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
];
