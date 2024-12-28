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

use crate::error::Error;
use crate::parse_value;
use crate::RawJsonb;
use std::fmt::Display;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq)]
pub struct OwnedJsonb {
    pub(crate) data: Vec<u8>,
}

impl OwnedJsonb {
    pub fn new(data: Vec<u8>) -> OwnedJsonb {
        Self { data }
    }

    pub fn as_raw(&self) -> RawJsonb<'_> {
        RawJsonb::new(self.data.as_slice())
    }

    pub fn to_vec(self) -> Vec<u8> {
        self.data
    }
}

impl From<&[u8]> for OwnedJsonb {
    fn from(data: &[u8]) -> Self {
        Self {
            data: data.to_vec(),
        }
    }
}

impl From<Vec<u8>> for OwnedJsonb {
    fn from(data: Vec<u8>) -> Self {
        Self { data }
    }
}

impl FromStr for OwnedJsonb {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let value = parse_value(s.as_bytes())?;
        let mut data = Vec::new();
        value.write_to_vec(&mut data);
        Ok(Self { data })
    }
}

impl AsRef<[u8]> for OwnedJsonb {
    fn as_ref(&self) -> &[u8] {
        self.data.as_ref()
    }
}

impl Display for OwnedJsonb {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let raw_jsonb = self.as_raw();
        write!(f, "{}", raw_jsonb.to_string())
    }
}
