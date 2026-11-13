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

//! Reference implementations of `RawJsonb` functions on `Value`.
//!
//! Each model follows the function's documentation with the simplest code that
//! does so, so a disagreement with the JSONB implementation is a bug in one of
//! them. `None` stands for an error result.

use std::borrow::Cow;
use std::collections::BTreeSet;

use jsonb::Value;

fn is_container(value: &Value<'_>) -> bool {
    matches!(value, Value::Array(_) | Value::Object(_))
}

/// Scalars that `contains` compares by value; extension values never match.
fn is_basic_scalar(value: &Value<'_>) -> bool {
    matches!(
        value,
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_)
    )
}

pub fn get_by_name<'a>(value: &Value<'a>, name: &str, ignore_case: bool) -> Option<Value<'a>> {
    let Value::Object(object) = value else {
        return None;
    };
    if let Some(found) = object.get(name) {
        return Some(found.clone());
    }
    if !ignore_case {
        return None;
    }
    object
        .iter()
        .find(|(key, _)| key.eq_ignore_ascii_case(name))
        .map(|(_, found)| found.clone())
}

pub fn object_keys(value: &Value<'_>) -> Option<Value<'static>> {
    let keys = value.as_object()?.keys();
    Some(Value::Array(
        keys.map(|key| Value::String(Cow::Owned(key.clone())))
            .collect(),
    ))
}

/// Removes object fields whose value is null, at every level; array elements
/// are kept even when null.
pub fn strip_nulls<'a>(value: &Value<'a>) -> Value<'a> {
    match value {
        Value::Array(items) => Value::Array(items.iter().map(strip_nulls).collect()),
        Value::Object(object) => Value::Object(
            object
                .iter()
                .filter(|(_, v)| !matches!(v, Value::Null))
                .map(|(k, v)| (k.clone(), strip_nulls(v)))
                .collect(),
        ),
        scalar => scalar.clone(),
    }
}

/// Removes the key from an object, or string elements equal to `name` from an
/// array. Scalars are an error.
pub fn delete_by_name<'a>(value: &Value<'a>, name: &str) -> Option<Value<'a>> {
    match value {
        Value::Object(object) => {
            let mut object = object.clone();
            object.remove(name);
            Some(Value::Object(object))
        }
        Value::Array(items) => Some(Value::Array(
            items
                .iter()
                .filter(|item| !matches!(item, Value::String(s) if s == name))
                .cloned()
                .collect(),
        )),
        _ => None,
    }
}

/// Removes the element at `index`, counting from the end when negative. An
/// out-of-range index leaves the array unchanged; non-arrays are an error.
pub fn delete_by_index<'a>(value: &Value<'a>, index: i32) -> Option<Value<'a>> {
    let mut items = value.as_array()?.clone();
    let len = items.len() as i64;
    let index = if index < 0 {
        len + i64::from(index)
    } else {
        i64::from(index)
    };
    if (0..len).contains(&index) {
        items.remove(index as usize);
    }
    Some(Value::Array(items))
}

/// Keys of an object, string elements of an array, or a string scalar itself.
fn key_set<'v>(value: &'v Value<'_>) -> BTreeSet<&'v str> {
    match value {
        Value::Object(object) => object.keys().map(String::as_str).collect(),
        Value::Array(items) => items
            .iter()
            .filter_map(|item| match item {
                Value::String(s) => Some(s.as_ref()),
                _ => None,
            })
            .collect(),
        Value::String(s) => BTreeSet::from([s.as_ref()]),
        _ => BTreeSet::new(),
    }
}

pub fn exists_any_keys(value: &Value<'_>, keys: &[&str]) -> bool {
    let set = key_set(value);
    keys.iter().any(|key| set.contains(key))
}

pub fn exists_all_keys(value: &Value<'_>, keys: &[&str]) -> bool {
    let set = key_set(value);
    keys.iter().all(|key| set.contains(key))
}

pub fn object_delete<'a>(value: &Value<'a>, keys: &BTreeSet<&str>) -> Option<Value<'a>> {
    filter_object(value, |key| !keys.contains(key))
}

pub fn object_pick<'a>(value: &Value<'a>, keys: &BTreeSet<&str>) -> Option<Value<'a>> {
    filter_object(value, |key| keys.contains(key))
}

/// Keeps the fields whose key passes `keep`; non-objects are an error.
fn filter_object<'a>(value: &Value<'a>, keep: impl Fn(&str) -> bool) -> Option<Value<'a>> {
    let object = value.as_object()?;
    let kept = object.iter().filter(|(k, _)| keep(k));
    Some(Value::Object(
        kept.map(|(k, v)| (k.clone(), v.clone())).collect(),
    ))
}

/// Inserts `key`, replacing an existing value only with `update`. Inserting
/// an existing key without `update`, or into a non-object, is an error.
pub fn object_insert<'a>(
    value: &Value<'a>,
    key: &str,
    new_value: &Value<'a>,
    update: bool,
) -> Option<Value<'a>> {
    let mut object = value.as_object()?.clone();
    if object.contains_key(key) && !update {
        return None;
    }
    object.insert(key.to_string(), new_value.clone());
    Some(Value::Object(object))
}

/// Merges two objects (right wins) or appends arrays; a non-array operand
/// becomes a single element.
pub fn concat<'a>(left: &Value<'a>, right: &Value<'a>) -> Value<'a> {
    match (left, right) {
        (Value::Object(l), Value::Object(r)) => {
            let mut merged = l.clone();
            merged.extend(r.iter().map(|(k, v)| (k.clone(), v.clone())));
            Value::Object(merged)
        }
        (l, r) => {
            let mut items = match l {
                Value::Array(items) => items.clone(),
                other => vec![other.clone()],
            };
            match r {
                Value::Array(more) => items.extend(more.iter().cloned()),
                other => items.push(other.clone()),
            }
            Value::Array(items)
        }
    }
}

/// PostgreSQL-style containment (`@>`).
///
/// Objects contain objects whose every field they have with a contained (for
/// containers) or equal (otherwise) value. Arrays contain arrays whose every
/// scalar they have and whose every container some element of theirs
/// contains, and contain a basic scalar they have as an element. Two basic
/// scalars contain each other when equal.
pub fn contains(left: &Value<'_>, right: &Value<'_>) -> bool {
    match (left, right) {
        (Value::Object(l), Value::Object(r)) => r.iter().all(|(key, r_value)| {
            l.get(key).is_some_and(|l_value| {
                if is_container(l_value) && is_container(r_value) {
                    contains(l_value, r_value)
                } else {
                    l_value == r_value
                }
            })
        }),
        (Value::Array(l), Value::Array(r)) => r.iter().all(|r_item| {
            if is_container(r_item) {
                l.iter()
                    .any(|l_item| is_container(l_item) && contains(l_item, r_item))
            } else {
                l.iter()
                    .any(|l_item| !is_container(l_item) && l_item == r_item)
            }
        }),
        (Value::Array(l), r) if is_basic_scalar(r) => {
            l.iter().any(|l_item| !is_container(l_item) && l_item == r)
        }
        (l, r) if is_basic_scalar(l) && is_basic_scalar(r) => l == r,
        _ => false,
    }
}
