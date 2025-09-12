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
use std::cmp::Ordering;

use crate::error::*;
use crate::ExtensionValue;
use crate::Number;
use crate::OwnedJsonb;
use crate::RawJsonb;

/// The value type of JSONB data.
#[derive(Debug, Clone, Copy)]
pub enum JsonbItemType {
    /// The Null JSONB type.
    Null,
    /// The Boolean JSONB type.
    Boolean,
    /// The Number JSONB type.
    Number,
    /// The String JSONB type.
    String,
    /// The Extension JSONB type.
    Extension,
    /// The Array JSONB type with the length of items.
    Array(usize),
    /// The Object JSONB type with the length of key and value pairs.
    Object(usize),
}

impl Eq for JsonbItemType {}

impl PartialEq for JsonbItemType {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl PartialOrd for JsonbItemType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (JsonbItemType::Null, JsonbItemType::Null) => Some(Ordering::Equal),
            (JsonbItemType::Null, _) => Some(Ordering::Greater),
            (_, JsonbItemType::Null) => Some(Ordering::Less),

            (JsonbItemType::Array(_), JsonbItemType::Array(_)) => None,
            (JsonbItemType::Array(_), _) => Some(Ordering::Greater),
            (_, JsonbItemType::Array(_)) => Some(Ordering::Less),

            (JsonbItemType::Object(_), JsonbItemType::Object(_)) => None,
            (JsonbItemType::Object(_), _) => Some(Ordering::Greater),
            (_, JsonbItemType::Object(_)) => Some(Ordering::Less),

            (JsonbItemType::String, JsonbItemType::String) => None,
            (JsonbItemType::String, _) => Some(Ordering::Greater),
            (_, JsonbItemType::String) => Some(Ordering::Less),

            (JsonbItemType::Number, JsonbItemType::Number) => None,
            (JsonbItemType::Number, _) => Some(Ordering::Greater),
            (_, JsonbItemType::Number) => Some(Ordering::Less),

            (JsonbItemType::Boolean, JsonbItemType::Boolean) => None,
            (JsonbItemType::Boolean, _) => Some(Ordering::Greater),
            (_, JsonbItemType::Boolean) => Some(Ordering::Less),

            (JsonbItemType::Extension, JsonbItemType::Extension) => None,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum NumberItem<'a> {
    /// Represents a raw JSONB number, stored as a byte slice.
    Raw(&'a [u8]),
    /// Represents a JSONB number.
    #[allow(dead_code)]
    Number(Number),
}

impl NumberItem<'_> {
    pub(crate) fn as_number(&self) -> Result<Number> {
        match self {
            NumberItem::Raw(data) => {
                let num = Number::decode(data)?;
                Ok(num)
            }
            NumberItem::Number(num) => Ok(num.clone()),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum ExtensionItem<'a> {
    /// Represents a raw JSONB extension value, stored as a byte slice.
    Raw(&'a [u8]),
    /// Represents a raw JSONB extension value.
    #[allow(dead_code)]
    Extension(ExtensionValue<'a>),
}

impl<'a> ExtensionItem<'a> {
    pub(crate) fn as_extension_value(&self) -> Result<ExtensionValue<'a>> {
        match self {
            ExtensionItem::Raw(data) => {
                let val = ExtensionValue::decode(data)?;
                Ok(val)
            }
            ExtensionItem::Extension(val) => Ok(val.clone()),
        }
    }
}

/// `JsonbItem` is an internal enum used primarily within `ArrayIterator` and
/// `ObjectIterator` to represent temporary values during iteration. It is also
/// utilized by `ArrayBuilder` and `ObjectBuilder` to store intermediate variables
/// during the construction of JSONB objects and arrays.
///
/// This enum encapsulates different types of JSONB values, allowing iterators and
/// builders to handle various data types uniformly. It supports null values,
/// booleans, numbers (represented as byte slices), strings (represented as byte slices),
/// raw JSONB data (`RawJsonb`), and owned JSONB data (`OwnedJsonb`).
#[derive(Debug, Clone)]
pub(crate) enum JsonbItem<'a> {
    /// Represents a JSONB null value.
    Null,
    /// Represents a JSONB boolean value.
    Boolean(bool),
    /// Represents a JSONB number, stored as a byte slice.
    Number(NumberItem<'a>),
    /// Represents a JSONB string.
    String(Cow<'a, str>),
    /// Represents a JSONB extension values, stored as a byte slice.
    Extension(ExtensionItem<'a>),
    /// Represents raw JSONB data, using a borrowed slice.
    Raw(RawJsonb<'a>),
    /// Represents owned JSONB data.
    Owned(OwnedJsonb),
}

impl<'a> JsonbItem<'a> {
    pub(crate) fn jsonb_item_type(&self) -> Result<JsonbItemType> {
        match self {
            JsonbItem::Null => Ok(JsonbItemType::Null),
            JsonbItem::Boolean(_) => Ok(JsonbItemType::Boolean),
            JsonbItem::Number(_) => Ok(JsonbItemType::Number),
            JsonbItem::String(_) => Ok(JsonbItemType::String),
            JsonbItem::Extension(_) => Ok(JsonbItemType::Extension),
            JsonbItem::Raw(raw) => raw.jsonb_item_type(),
            JsonbItem::Owned(owned) => owned.as_raw().jsonb_item_type(),
        }
    }

    pub(crate) fn as_raw_jsonb(&self) -> Option<RawJsonb<'a>> {
        match self {
            JsonbItem::Raw(raw_jsonb) => Some(*raw_jsonb),
            _ => None,
        }
    }

    pub(crate) fn as_null(&self) -> Option<()> {
        match self {
            JsonbItem::Null => Some(()),
            _ => None,
        }
    }

    pub(crate) fn as_str(&self) -> Option<Cow<'a, str>> {
        match self {
            JsonbItem::String(s) => Some(s.clone()),
            _ => None,
        }
    }
}

impl Eq for JsonbItem<'_> {}

impl PartialEq for JsonbItem<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

#[allow(clippy::non_canonical_partial_ord_impl)]
impl PartialOrd for JsonbItem<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let self_type = self.jsonb_item_type().ok()?;
        let other_type = other.jsonb_item_type().ok()?;

        // First use JSONB type to determine the order,
        // different types must have different orders.
        if let Some(ord) = self_type.partial_cmp(&other_type) {
            return Some(ord);
        }

        let self_item = if let JsonbItem::Owned(owned) = self {
            &JsonbItem::Raw(owned.as_raw())
        } else {
            self
        };
        let other_item = if let JsonbItem::Owned(owned) = other {
            &JsonbItem::Raw(owned.as_raw())
        } else {
            other
        };

        match (self_item, other_item) {
            (JsonbItem::Raw(self_raw), JsonbItem::Raw(other_raw)) => {
                self_raw.partial_cmp(other_raw)
            }
            // compare null, raw jsonb must not null
            (JsonbItem::Raw(_), JsonbItem::Null) => Some(Ordering::Less),
            (JsonbItem::Null, JsonbItem::Raw(_)) => Some(Ordering::Greater),
            // compare extension
            (JsonbItem::Extension(self_ext), JsonbItem::Extension(other_ext)) => {
                let self_val = self_ext.as_extension_value().ok()?;
                let other_val = other_ext.as_extension_value().ok()?;
                self_val.partial_cmp(&other_val)
            }
            (JsonbItem::Raw(self_raw), JsonbItem::Extension(other_ext)) => {
                let self_val = self_raw.as_extension_value();
                let other_val = other_ext.as_extension_value().ok()?;
                if let Ok(Some(self_val)) = self_val {
                    self_val.partial_cmp(&other_val)
                } else {
                    None
                }
            }
            (JsonbItem::Extension(self_ext), JsonbItem::Raw(other_raw)) => {
                let self_val = self_ext.as_extension_value().ok()?;
                let other_val = other_raw.as_extension_value();
                if let Ok(Some(other_val)) = other_val {
                    self_val.partial_cmp(&other_val)
                } else {
                    None
                }
            }
            // compare boolean
            (JsonbItem::Boolean(self_val), JsonbItem::Boolean(other_val)) => {
                self_val.partial_cmp(other_val)
            }
            (JsonbItem::Raw(self_raw), JsonbItem::Boolean(other_val)) => {
                let self_val = self_raw.as_bool();
                if let Ok(Some(self_val)) = self_val {
                    self_val.partial_cmp(other_val)
                } else {
                    None
                }
            }
            (JsonbItem::Boolean(self_val), JsonbItem::Raw(other_raw)) => {
                let other_val = other_raw.as_bool();
                if let Ok(Some(other_val)) = other_val {
                    self_val.partial_cmp(&other_val)
                } else {
                    None
                }
            }
            // compare number
            (JsonbItem::Number(self_num), JsonbItem::Number(other_num)) => {
                let self_val = self_num.as_number().ok()?;
                let other_val = other_num.as_number().ok()?;
                self_val.partial_cmp(&other_val)
            }
            (JsonbItem::Raw(self_raw), JsonbItem::Number(other_num)) => {
                let self_val = self_raw.as_number();
                let other_val = other_num.as_number().ok()?;
                if let Ok(Some(self_val)) = self_val {
                    self_val.partial_cmp(&other_val)
                } else {
                    None
                }
            }
            (JsonbItem::Number(self_num), JsonbItem::Raw(other_raw)) => {
                let self_val = self_num.as_number().ok()?;
                let other_val = other_raw.as_number();
                if let Ok(Some(other_val)) = other_val {
                    self_val.partial_cmp(&other_val)
                } else {
                    None
                }
            }
            // compare string
            (JsonbItem::String(self_str), JsonbItem::String(other_str)) => {
                self_str.partial_cmp(other_str)
            }
            (JsonbItem::Raw(self_raw), JsonbItem::String(other_str)) => {
                let self_str = self_raw.as_str();
                if let Ok(Some(self_str)) = self_str {
                    self_str.partial_cmp(other_str)
                } else {
                    None
                }
            }
            (JsonbItem::String(self_str), JsonbItem::Raw(other_raw)) => {
                let other_str = other_raw.as_str();
                if let Ok(Some(other_str)) = other_str {
                    self_str.partial_cmp(&other_str)
                } else {
                    None
                }
            }
            (_, _) => None,
        }
    }
}

impl Ord for JsonbItem<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(ordering) => ordering,
            None => Ordering::Equal,
        }
    }
}
