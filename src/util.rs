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

use std::io::Read;

use super::constants::*;
use super::error::Error;
use super::error::ParseErrorCode;

#[allow(clippy::zero_prefixed_literal)]
static HEX: [u8; 256] = {
    const __: u8 = 255; // not a hex digit
    [
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 0
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 1
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 2
        00, 01, 02, 03, 04, 05, 06, 07, 08, 09, __, __, __, __, __, __, // 3
        __, 10, 11, 12, 13, 14, 15, __, __, __, __, __, __, __, __, __, // 4
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 5
        __, 10, 11, 12, 13, 14, 15, __, __, __, __, __, __, __, __, __, // 6
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
        __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
    ]
};

pub fn parse_escaped_string<'a>(
    mut data: &'a [u8],
    idx: &mut usize,
    str_buf: &mut String,
) -> Result<&'a [u8], Error> {
    let byte = data[0];
    *idx += 1;
    data = &data[1..];
    match byte {
        b'\\' => str_buf.push(BS),
        b'"' => str_buf.push(QU),
        b'/' => str_buf.push(SD),
        b'b' => str_buf.push(BB),
        b'f' => str_buf.push(FF),
        b'n' => str_buf.push(NN),
        b'r' => str_buf.push(RR),
        b't' => str_buf.push(TT),
        b'u' => {
            let mut numbers = vec![0; UNICODE_LEN];
            if data[0] == b'{' {
                data = &data[1..];
                data.read_exact(numbers.as_mut_slice())?;
                if data[0] != b'}' {
                    return Err(Error::Syntax(
                        ParseErrorCode::UnexpectedEndOfHexEscape,
                        *idx,
                    ));
                }
                data = &data[1..];
                *idx += 6;
            } else {
                data.read_exact(numbers.as_mut_slice())?;
                *idx += 4;
            }
            let hex = decode_hex_escape(numbers.clone(), idx)?;

            let c = match hex {
                0xDC00..=0xDFFF => {
                    encode_invalid_unicode(numbers, str_buf);
                    return Ok(data);
                }

                // Non-BMP characters are encoded as a sequence of two hex
                // escapes, representing UTF-16 surrogates. If deserializing a
                // utf-8 string the surrogates are required to be paired,
                // whereas deserializing a byte string accepts lone surrogates.
                n1 @ 0xD800..=0xDBFF => {
                    if data.len() < 2 {
                        encode_invalid_unicode(numbers, str_buf);
                        return Ok(data);
                    }
                    if data[0] == b'\\' && data[1] == b'u' {
                        *idx += 2;
                        data = &data[2..];
                    } else {
                        encode_invalid_unicode(numbers, str_buf);
                        return Ok(data);
                    }
                    let mut lower_numbers = vec![0; UNICODE_LEN];
                    if data[0] == b'{' {
                        data = &data[1..];
                        data.read_exact(lower_numbers.as_mut_slice())?;
                        if data[0] != b'}' {
                            return Err(Error::Syntax(
                                ParseErrorCode::UnexpectedEndOfHexEscape,
                                *idx,
                            ));
                        }
                        data = &data[1..];
                        *idx += 6;
                    } else {
                        data.read_exact(lower_numbers.as_mut_slice())?;
                        *idx += 4;
                    }
                    let n2 = decode_hex_escape(lower_numbers.clone(), idx)?;
                    if !(0xDC00..=0xDFFF).contains(&n2) {
                        encode_invalid_unicode(numbers, str_buf);
                        encode_invalid_unicode(lower_numbers, str_buf);
                        return Ok(data);
                    }

                    let n = (((n1 - 0xD800) as u32) << 10 | (n2 - 0xDC00) as u32) + 0x1_0000;
                    char::from_u32(n).unwrap()
                }

                // Every u16 outside of the surrogate ranges above is guaranteed
                // to be a legal char.
                n => char::from_u32(n as u32).unwrap(),
            };
            str_buf.push(c);
        }
        other => return Err(Error::Syntax(ParseErrorCode::InvalidEscaped(other), *idx)),
    }
    Ok(data)
}

// https://datatracker.ietf.org/doc/html/rfc8259#section-8.2
// RFC8259 allow invalid Unicode
#[inline]
fn encode_invalid_unicode(numbers: Vec<u8>, str_buf: &mut String) {
    str_buf.push('\\');
    str_buf.push('u');
    for n in numbers {
        str_buf.push(n.into());
    }
}

#[inline]
fn decode_hex_val(val: u8) -> Option<u16> {
    let n = HEX[val as usize] as u16;
    if n == 255 {
        None
    } else {
        Some(n)
    }
}

#[inline]
fn decode_hex_escape(numbers: Vec<u8>, idx: &usize) -> Result<u16, Error> {
    let mut n = 0;
    for number in numbers {
        if let Some(hex) = decode_hex_val(number) {
            n = (n << 4) + hex;
        } else {
            return Err(Error::Syntax(ParseErrorCode::InvalidHex(number), *idx));
        }
    }
    Ok(n)
}
