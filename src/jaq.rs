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
use std::str;

use jaq_json::Map;
use jaq_json::Num;
use jaq_json::Val;
use num_traits::ToPrimitive;

use crate::constants::enter_container;
use crate::constants::DECIMAL128_MAX;
use crate::constants::DECIMAL128_MIN;
use crate::constants::MAX_DECIMAL256_PRECISION;
use crate::core::ArrayBuilder;
use crate::core::ArrayIterator;
use crate::core::ExtensionItem;
use crate::core::JsonbItem;
use crate::core::JsonbItemType;
use crate::core::NumberItem;
use crate::core::ObjectBuilder;
use crate::core::ObjectIterator;
use crate::error::Result;
use crate::Decimal128;
use crate::Decimal256;
use crate::Error;
use crate::ExtensionValue;
use crate::Number;
use crate::OwnedJsonb;
use crate::RawJsonb;
use ethnum::i256;

/// Convert raw JSONB directly into jaq-json's native value type.
impl<'a> TryFrom<RawJsonb<'a>> for Val {
    type Error = Error;

    fn try_from(raw: RawJsonb<'a>) -> Result<Self> {
        let item = JsonbItem::from_raw_jsonb(raw)?;
        jsonb_item_to_jaq_val(item, 0)
    }
}

/// Converts an item to a jaq value, where `depth` is the number of enclosing containers.
fn jsonb_item_to_jaq_val(item: JsonbItem<'_>, depth: usize) -> Result<Val> {
    match item {
        JsonbItem::Null => Ok(Val::Null),
        JsonbItem::Boolean(value) => Ok(Val::Bool(value)),
        JsonbItem::Number(value) => value.as_number().map(number_to_jaq_num).map(Val::Num),
        JsonbItem::String(value) => Ok(Val::utf8_str(value.as_bytes().to_vec())),
        JsonbItem::Extension(value) => match value.as_extension_value()? {
            ExtensionValue::Binary(value) => Ok(Val::byte_str(value.to_vec())),
            value => Ok(Val::utf8_str(value.to_string().into_bytes())),
        },
        JsonbItem::Raw(raw) => raw_container_to_jaq_val(raw, depth),
        JsonbItem::Owned(owned) => raw_container_to_jaq_val(owned.as_raw(), depth),
    }
}

fn raw_container_to_jaq_val(raw: RawJsonb<'_>, depth: usize) -> Result<Val> {
    match raw.jsonb_item_type()? {
        JsonbItemType::Array(len) => {
            let depth = enter_container(depth)?;
            let iter = ArrayIterator::new_with_len(raw, len);
            let values = iter
                .map(|item| item.and_then(|item| jsonb_item_to_jaq_val(item, depth)))
                .collect::<Result<Vec<_>>>()?;
            Ok(Val::Arr(jaq_json::Rc::new(values)))
        }
        JsonbItemType::Object(len) => {
            let depth = enter_container(depth)?;
            let iter = ObjectIterator::new_with_len(raw, len)?;
            let mut values = Map::with_capacity_and_hasher(iter.len(), Default::default());
            for item in iter {
                let (key, value) = item?;
                values.insert(
                    Val::utf8_str(key.as_bytes().to_vec()),
                    jsonb_item_to_jaq_val(value, depth)?,
                );
            }
            Ok(Val::obj(values))
        }
        _ => jsonb_item_to_jaq_val(JsonbItem::from_raw_jsonb(raw)?, depth),
    }
}

fn number_to_jaq_num(number: Number) -> Num {
    match number {
        Number::Int64(value) => Num::from_integral(value),
        Number::UInt64(value) => Num::from_integral(value),
        Number::Float64(value) => Num::Float(value),
        Number::Decimal64(_) | Number::Decimal128(_) | Number::Decimal256(_) => {
            Num::Dec(jaq_json::Rc::new(number.to_string()))
        }
    }
}

/// Convert a jaq-json value back into JSONB.
impl TryFrom<&Val> for OwnedJsonb {
    type Error = Error;

    fn try_from(value: &Val) -> Result<Self> {
        jaq_val_to_owned_jsonb(value)
    }
}

fn jaq_val_to_owned_jsonb(value: &Val) -> Result<OwnedJsonb> {
    match value {
        Val::Arr(values) => {
            let mut builder = ArrayBuilder::with_capacity(values.len());
            for value in values.iter() {
                builder.push_jsonb_item(jaq_val_to_jsonb_item(value)?);
            }
            builder.build()
        }
        Val::Obj(values) => {
            let mut entries = Vec::with_capacity(values.len());
            for (key, value) in values.iter() {
                let key = jaq_val_to_object_key(key)?;
                entries.push((key.into_owned(), jaq_val_to_jsonb_item(value)?));
            }
            ObjectBuilder::build_from_entries(entries)
        }
        value => OwnedJsonb::from_item(jaq_val_to_jsonb_item(value)?),
    }
}

fn jaq_val_to_jsonb_item(value: &Val) -> Result<JsonbItem<'_>> {
    match value {
        Val::Null => Ok(JsonbItem::Null),
        Val::Bool(value) => Ok(JsonbItem::Boolean(*value)),
        Val::Num(value) => Ok(JsonbItem::Number(NumberItem::Number(jaq_num_to_number(
            value,
        )?))),
        Val::TStr(value) => Ok(JsonbItem::String(bytes_to_string(value.as_ref())?)),
        Val::BStr(value) => Ok(JsonbItem::Extension(ExtensionItem::Extension(
            ExtensionValue::Binary(value.as_ref()),
        ))),
        Val::Arr(_) | Val::Obj(_) => Ok(JsonbItem::Owned(jaq_val_to_owned_jsonb(value)?)),
    }
}

fn jaq_val_to_object_key(value: &Val) -> Result<Cow<'_, str>> {
    match value {
        Val::TStr(value) | Val::BStr(value) => bytes_to_string(value.as_ref()),
        _ => Err(Error::InvalidObject),
    }
}

fn bytes_to_string(value: &[u8]) -> Result<Cow<'_, str>> {
    str::from_utf8(value)
        .map(Cow::Borrowed)
        .map_err(|_| Error::InvalidObject)
}

fn jaq_num_to_number(value: &Num) -> Result<Number> {
    match value {
        Num::Int(value) => Ok(Number::Int64(*value as i64)),
        Num::BigInt(value) => {
            if let Some(value) = value.to_i64() {
                return Ok(Number::Int64(value));
            }
            if let Some(value) = value.to_u64() {
                return Ok(Number::UInt64(value));
            }
            if let Some(value) = value.to_i128() {
                if (DECIMAL128_MIN..=DECIMAL128_MAX).contains(&value) {
                    return Ok(Number::Decimal128(Decimal128 { scale: 0, value }));
                }
            }
            let value_string = value.to_string();
            let digits = value_string.trim_start_matches('-').len();
            if digits <= MAX_DECIMAL256_PRECISION {
                let value = value_string
                    .parse::<i256>()
                    .map_err(|_| Error::InvalidJsonbNumber)?;
                return Ok(Number::Decimal256(Decimal256 { scale: 0, value }));
            }
            Err(Error::InvalidJsonbNumber)
        }
        Num::Float(value) => Ok(Number::Float64(*value)),
        Num::Dec(value) => crate::parse_owned_jsonb(value.as_bytes())
            .and_then(|value| value.as_raw().as_number()?.ok_or(Error::InvalidJsonbNumber)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big_int(value: &str) -> Num {
        Num::from_str_radix(value, 10).unwrap()
    }

    #[test]
    fn try_from_converts_between_raw_jsonb_and_jaq_val() {
        let jsonb =
            r#"{"name":"alice","scores":[1,2,3],"valid":true}"#.parse::<OwnedJsonb>().unwrap();

        let value = Val::try_from(jsonb.as_raw()).unwrap();
        let converted = OwnedJsonb::try_from(&value).unwrap();

        assert_eq!(
            converted.to_string(),
            r#"{"name":"alice","scores":[1,2,3],"valid":true}"#
        );
    }

    #[test]
    fn jaq_bigint_to_number_preserves_decimal128_range() {
        let value = jaq_num_to_number(&big_int("18446744073709551616")).unwrap();

        match value {
            Number::Decimal128(value) => {
                assert_eq!(value.scale, 0);
                assert_eq!(value.value, 18_446_744_073_709_551_616_i128);
            }
            other => panic!("expected Decimal128, got {other:?}"),
        }
    }

    #[test]
    fn jaq_bigint_to_number_preserves_decimal256_range() {
        let value = "100000000000000000000000000000000000000";
        let number = jaq_num_to_number(&big_int(value)).unwrap();

        match number {
            Number::Decimal256(value) => {
                assert_eq!(value.scale, 0);
                assert_eq!(
                    value.value.to_string(),
                    "100000000000000000000000000000000000000"
                );
            }
            other => panic!("expected Decimal256, got {other:?}"),
        }
    }

    #[test]
    fn jaq_bigint_to_number_rejects_values_outside_decimal256_range() {
        let value = "1".repeat(MAX_DECIMAL256_PRECISION + 1);
        let err = jaq_num_to_number(&big_int(&value)).unwrap_err();

        assert_eq!(err, Error::InvalidJsonbNumber);
    }
}
