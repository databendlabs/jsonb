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
use std::fmt::Display;
use std::fmt::Formatter;

use nom::branch::alt;
use nom::character::complete::char;
use nom::character::complete::i32;
use nom::character::complete::multispace0;
use nom::combinator::map;
use nom::multi::separated_list1;
use nom::sequence::delimited;
use nom::sequence::preceded;
use nom::sequence::terminated;
use nom::IResult;
use nom::Parser;

use crate::jsonpath::raw_string;
use crate::jsonpath::string;
use crate::Error;

/// Represents a set of key path chains.
/// Compatible with PostgreSQL extracts JSON sub-object paths syntax.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct KeyPaths<'a> {
    pub paths: Vec<KeyPath<'a>>,
}

/// Represents a valid key path.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum KeyPath<'a> {
    /// represents the index of an Array, allow negative indexing.
    Index(i32),
    /// represents the quoted field name of an Object.
    QuotedName(Cow<'a, str>),
    /// represents the field name of an Object.
    Name(Cow<'a, str>),
}

impl Display for KeyPaths<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, path) in self.paths.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "{path}")?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl Display for KeyPath<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            KeyPath::Index(idx) => {
                write!(f, "{idx}")?;
            }
            KeyPath::QuotedName(name) => {
                write!(f, "\"{name}\"")?;
            }
            KeyPath::Name(name) => {
                write!(f, "{name}")?;
            }
        }
        Ok(())
    }
}

/// Parsing the input string to key paths.
pub fn parse_key_paths(input: &[u8]) -> Result<KeyPaths<'_>, Error> {
    match key_paths(input) {
        Ok((rest, paths)) => {
            if !rest.is_empty() {
                return Err(Error::InvalidKeyPath);
            }
            let key_paths = KeyPaths { paths };
            Ok(key_paths)
        }
        Err(nom::Err::Error(_) | nom::Err::Failure(_)) => Err(Error::InvalidKeyPath),
        Err(nom::Err::Incomplete(_)) => unreachable!(),
    }
}

fn key_path(input: &[u8]) -> IResult<&[u8], KeyPath<'_>> {
    alt((
        map(i32, KeyPath::Index),
        map(string, KeyPath::QuotedName),
        map(raw_string, KeyPath::Name),
    ))
    .parse(input)
}

fn key_paths(input: &[u8]) -> IResult<&[u8], Vec<KeyPath<'_>>> {
    alt((
        delimited(
            preceded(multispace0, char('{')),
            separated_list1(char(','), delimited(multispace0, key_path, multispace0)),
            terminated(char('}'), multispace0),
        ),
        map(
            delimited(
                preceded(multispace0, char('{')),
                multispace0,
                terminated(char('}'), multispace0),
            ),
            |_| vec![],
        ),
    ))
    .parse(input)
}
