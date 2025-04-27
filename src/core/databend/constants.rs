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

// JSONB header constants
pub(super) const ARRAY_CONTAINER_TAG: u32 = 0x80000000;
pub(super) const OBJECT_CONTAINER_TAG: u32 = 0x40000000;
pub(super) const SCALAR_CONTAINER_TAG: u32 = 0x20000000;

pub(super) const CONTAINER_HEADER_TYPE_MASK: u32 = 0xE0000000;
pub(super) const CONTAINER_HEADER_LEN_MASK: u32 = 0x1FFFFFFF;

// JSONB JEntry constants
pub(super) const NULL_TAG: u32 = 0x00000000;
pub(super) const STRING_TAG: u32 = 0x10000000;
pub(super) const NUMBER_TAG: u32 = 0x20000000;
pub(super) const FALSE_TAG: u32 = 0x30000000;
pub(super) const TRUE_TAG: u32 = 0x40000000;
pub(super) const CONTAINER_TAG: u32 = 0x50000000;
pub(super) const EXTENSION_TAG: u32 = 0x60000000;

// JSONB number constants
pub(super) const NUMBER_ZERO: u8 = 0x00;
pub(super) const NUMBER_NAN: u8 = 0x10;
pub(super) const NUMBER_INF: u8 = 0x20;
pub(super) const NUMBER_NEG_INF: u8 = 0x30;
pub(super) const NUMBER_INT: u8 = 0x40;
pub(super) const NUMBER_UINT: u8 = 0x50;
pub(super) const NUMBER_FLOAT: u8 = 0x60;
pub(super) const NUMBER_DECIMAL: u8 = 0x70;

// JSONB extension constants
pub(super) const EXTENSION_BINARY: u8 = 0x00;
pub(super) const EXTENSION_DATE: u8 = 0x10;
pub(super) const EXTENSION_TIMESTAMP: u8 = 0x20;
pub(super) const EXTENSION_TIMESTAMP_TZ: u8 = 0x30;
pub(super) const EXTENSION_INTERVAL: u8 = 0x40;

// @todo support offset mode
#[allow(dead_code)]
pub(super) const JENTRY_IS_OFF_FLAG: u32 = 0x80000000;
pub(super) const JENTRY_TYPE_MASK: u32 = 0x70000000;
pub(super) const JENTRY_OFF_LEN_MASK: u32 = 0x0FFFFFFF;
