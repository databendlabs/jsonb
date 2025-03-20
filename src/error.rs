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

use core::fmt::Display;

use serde::de;
use serde::ser;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParseErrorCode {
    InvalidEOF,
    InvalidNumberValue,
    InvalidStringValue,
    ExpectedSomeIdent,
    ExpectedSomeValue,
    ExpectedColon,
    ExpectedArrayCommaOrEnd,
    ExpectedObjectCommaOrEnd,
    UnexpectedTrailingCharacters,
    KeyMustBeAString,
    ControlCharacterWhileParsingString,
    InvalidEscaped(u8),
    InvalidHex(u8),
    InvalidLoneLeadingSurrogateInHexEscape(u16),
    InvalidSurrogateInHexEscape(u16),
    UnexpectedEndOfHexEscape,
}

pub type Result<T> = std::result::Result<T, Error>;

impl Display for ParseErrorCode {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match *self {
            ParseErrorCode::InvalidEOF => f.write_str("EOF while parsing a value"),
            ParseErrorCode::InvalidNumberValue => f.write_str("invalid number"),
            ParseErrorCode::InvalidStringValue => f.write_str("invalid string"),
            ParseErrorCode::ExpectedSomeIdent => f.write_str("expected ident"),
            ParseErrorCode::ExpectedSomeValue => f.write_str("expected value"),
            ParseErrorCode::ExpectedColon => f.write_str("expected `:`"),
            ParseErrorCode::ExpectedArrayCommaOrEnd => f.write_str("expected `,` or `]`"),
            ParseErrorCode::ExpectedObjectCommaOrEnd => f.write_str("expected `,` or `}`"),
            ParseErrorCode::UnexpectedTrailingCharacters => f.write_str("trailing characters"),
            ParseErrorCode::KeyMustBeAString => f.write_str("key must be a string"),
            ParseErrorCode::ControlCharacterWhileParsingString => {
                f.write_str("control character (\\u0000-\\u001F) found while parsing a string")
            }
            ParseErrorCode::InvalidEscaped(n) => {
                write!(f, "invalid escaped '{:X}'", n)
            }
            ParseErrorCode::InvalidHex(n) => {
                write!(f, "invalid hex '{:X}'", n)
            }
            ParseErrorCode::InvalidLoneLeadingSurrogateInHexEscape(n) => {
                write!(f, "lone leading surrogate in hex escape '{:X}'", n)
            }
            ParseErrorCode::InvalidSurrogateInHexEscape(n) => {
                write!(f, "invalid surrogate in hex escape '{:X}'", n)
            }
            ParseErrorCode::UnexpectedEndOfHexEscape => f.write_str("unexpected end of hex escape"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Error {
    InvalidUtf8,
    InvalidEOF,
    InvalidToken,
    InvalidCast,

    InvalidJson,
    InvalidJsonb,
    InvalidJsonbHeader,
    InvalidJsonbJEntry,
    InvalidJsonbNumber,

    InvalidJsonPath,
    InvalidJsonPathPredicate,
    InvalidKeyPath,

    InvalidJsonType,
    InvalidObject,
    ObjectDuplicateKey,
    UnexpectedType,

    Message(String),
    Syntax(ParseErrorCode, usize),
}

impl ser::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::Message(msg.to_string())
    }
}

impl de::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::Message(msg.to_string())
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Message(m) => write!(f, "{}", m),
            Error::Syntax(code, pos) => write!(f, "{}, pos {}", code, pos),
            _ => write!(f, "{:?}", self),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        // match self {
        //    Error::JsonError(e) => Some(e),
        //    Error::Json5Error(e) => Some(e),
        //    Error::Io(e) => Some(e),
        //    Error::Utf8(e) => Some(e),
        //    _ => None,
        //}
        None
    }
}

impl From<std::io::Error> for Error {
    fn from(_error: std::io::Error) -> Self {
        Error::InvalidUtf8
    }
}

impl From<std::str::Utf8Error> for Error {
    fn from(_error: std::str::Utf8Error) -> Self {
        Error::InvalidUtf8
    }
}

impl From<nom::Err<nom::error::Error<&[u8]>>> for Error {
    fn from(_error: nom::Err<nom::error::Error<&[u8]>>) -> Self {
        Error::InvalidJsonb
    }
}
