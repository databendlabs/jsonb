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

use byteorder::BigEndian;
use byteorder::WriteBytesExt;

use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::VecDeque;

use crate::constants::*;
use crate::jsonpath::ArrayIndex;
use crate::jsonpath::BinaryOperator;
use crate::jsonpath::Expr;
use crate::jsonpath::Index;
use crate::jsonpath::JsonPath;
use crate::jsonpath::Path;
use crate::jsonpath::PathValue;
use crate::number::Number;

use nom::{
    bytes::complete::take, combinator::map, multi::count, number::complete::be_u32, IResult,
};

#[derive(Debug)]
enum Item<'a> {
    Container(&'a [u8]),
    Scalar(Vec<u8>),
}

#[derive(Debug)]
enum ExprValue<'a> {
    Values(Vec<PathValue<'a>>),
    Value(Box<PathValue<'a>>),
}

pub struct Selector<'a> {
    json_path: JsonPath<'a>,
}

impl<'a> Selector<'a> {
    pub fn new(json_path: JsonPath<'a>) -> Self {
        Self { json_path }
    }

    pub fn select(&'a self, value: &'a [u8]) -> Vec<Vec<u8>> {
        let root = value;
        let mut items = VecDeque::new();
        items.push_back(Item::Container(value));

        for path in self.json_path.paths.iter() {
            match path {
                &Path::Root => {
                    continue;
                }
                &Path::Current => unreachable!(),
                Path::FilterExpr(expr) => {
                    let mut tmp_items = Vec::with_capacity(items.len());
                    while let Some(item) = items.pop_front() {
                        let current = match item {
                            Item::Container(val) => val,
                            Item::Scalar(ref val) => val.as_slice(),
                        };
                        if self.filter_expr(root, current, expr) {
                            tmp_items.push(item);
                        }
                    }
                    while let Some(item) = tmp_items.pop() {
                        items.push_front(item);
                    }
                }
                _ => {
                    let len = items.len();
                    for _ in 0..len {
                        let item = items.pop_front().unwrap();
                        match item {
                            Item::Container(current) => {
                                self.select_path(current, path, &mut items);
                            }
                            Item::Scalar(_) => {
                                // In lax mode, bracket wildcard allow Scalar value.
                                if path == &Path::BracketWildcard {
                                    items.push_back(item);
                                }
                            }
                        }
                    }
                }
            }
        }
        let mut values = Vec::new();
        while let Some(item) = items.pop_front() {
            match item {
                Item::Container(val) => {
                    values.push(val.to_vec());
                }
                Item::Scalar(val) => {
                    values.push(val);
                }
            }
        }
        values
    }

    fn select_path(&'a self, current: &'a [u8], path: &Path<'a>, items: &mut VecDeque<Item<'a>>) {
        match path {
            Path::DotWildcard => {
                self.select_object_values(current, items);
            }
            Path::BracketWildcard => {
                self.select_array_values(current, items);
            }
            Path::ColonField(name) | Path::DotField(name) | Path::ObjectField(name) => {
                self.select_by_name(current, name, items);
            }
            Path::ArrayIndices(indices) => {
                self.select_by_indices(current, indices, items);
            }
            _ => unreachable!(),
        }
    }

    // select all values in an Object.
    fn select_object_values(&'a self, current: &'a [u8], items: &mut VecDeque<Item<'a>>) {
        let (rest, (ty, length)) = decode_header(current).unwrap();
        if ty != OBJECT_CONTAINER_TAG || length == 0 {
            return;
        }
        let (rest, key_jentries) = decode_jentries(rest, length).unwrap();
        let (rest, val_jentries) = decode_jentries(rest, length).unwrap();
        let mut offset = 0;
        for (_, length) in key_jentries.iter() {
            offset += length;
        }
        let rest = &rest[offset..];
        offset = 0;
        for (jty, jlength) in val_jentries.iter() {
            let val = &rest[offset..offset + jlength];
            let item = if *jty == CONTAINER_TAG {
                Item::Container(val)
            } else {
                let buf = Self::build_scalar_buf(*jty, *jlength, val);
                Item::Scalar(buf)
            };
            items.push_back(item);
            offset += jlength;
        }
    }

    // select all values in an Array.
    fn select_array_values(&'a self, current: &'a [u8], items: &mut VecDeque<Item<'a>>) {
        let (rest, (ty, length)) = decode_header(current).unwrap();
        if ty != ARRAY_CONTAINER_TAG {
            // In lax mode, bracket wildcard allow Scalar value.
            items.push_back(Item::Container(current));
            return;
        }
        let (rest, val_jentries) = decode_jentries(rest, length).unwrap();
        let mut offset = 0;
        for (jty, jlength) in val_jentries.iter() {
            let val = &rest[offset..offset + jlength];
            let item = if *jty == CONTAINER_TAG {
                Item::Container(val)
            } else {
                let buf = Self::build_scalar_buf(*jty, *jlength, val);
                Item::Scalar(buf)
            };
            items.push_back(item);
            offset += jlength;
        }
    }

    // select value in an Object by key name.
    fn select_by_name(&'a self, current: &'a [u8], name: &str, items: &mut VecDeque<Item<'a>>) {
        let (rest, (ty, length)) = decode_header(current).unwrap();
        if ty != OBJECT_CONTAINER_TAG || length == 0 {
            return;
        }
        let (rest, key_jentries) = decode_jentries(rest, length).unwrap();
        let (rest, val_jentries) = decode_jentries(rest, length).unwrap();
        let mut idx = 0;
        let mut offset = 0;
        let mut found = false;
        for (i, (_, jlength)) in key_jentries.iter().enumerate() {
            if name.len() != *jlength || found {
                offset += jlength;
                continue;
            }
            let (_, key) = decode_string(&rest[offset..], *jlength).unwrap();
            if name == unsafe { std::str::from_utf8_unchecked(key) } {
                found = true;
                idx = i;
            }
            offset += jlength;
        }
        if !found {
            return;
        }
        let rest = &rest[offset..];
        offset = 0;
        for (i, (jty, jlength)) in val_jentries.iter().enumerate() {
            if i != idx {
                offset += jlength;
                continue;
            }
            let val = &rest[offset..offset + jlength];
            let item = if *jty == CONTAINER_TAG {
                Item::Container(val)
            } else {
                let buf = Self::build_scalar_buf(*jty, *jlength, val);
                Item::Scalar(buf)
            };
            items.push_back(item);
            break;
        }
    }

    // select values in an Array by indices.
    fn select_by_indices(
        &'a self,
        current: &'a [u8],
        indices: &Vec<ArrayIndex>,
        items: &mut VecDeque<Item<'a>>,
    ) {
        let (rest, (ty, length)) = decode_header(current).unwrap();
        if ty != ARRAY_CONTAINER_TAG || length == 0 {
            return;
        }
        let mut val_indices = Vec::new();
        for index in indices {
            match index {
                ArrayIndex::Index(idx) => {
                    if let Some(idx) = Self::convert_index(idx, length as i32) {
                        val_indices.push(idx);
                    }
                }
                ArrayIndex::Slice((start, end)) => {
                    if let Some(mut idxes) = Self::convert_slice(start, end, length as i32) {
                        val_indices.append(&mut idxes);
                    }
                }
            }
        }
        if val_indices.is_empty() {
            return;
        }
        let (rest, jentries) = decode_jentries(rest, length).unwrap();
        let mut offset = 0;
        let mut offsets = Vec::with_capacity(jentries.len());
        for (_, jlength) in jentries.iter() {
            offsets.push(offset);
            offset += jlength;
        }
        for i in val_indices {
            let offset = offsets[i];
            let (jty, jlength) = jentries[i];
            let val = &rest[offset..offset + jlength];
            let item = if jty == CONTAINER_TAG {
                Item::Container(val)
            } else {
                let buf = Self::build_scalar_buf(jty, jlength, val);
                Item::Scalar(buf)
            };
            items.push_back(item);
        }
    }

    fn build_scalar_buf(jty: u32, jlength: usize, val: &'a [u8]) -> Vec<u8> {
        let mut buf = Vec::with_capacity(8 + jlength);
        buf.write_u32::<BigEndian>(SCALAR_CONTAINER_TAG).unwrap();
        let jentry = jty | jlength as u32;
        buf.write_u32::<BigEndian>(jentry).unwrap();
        buf.extend_from_slice(val);
        buf
    }

    // check and convert index to Array index.
    fn convert_index(index: &Index, length: i32) -> Option<usize> {
        let idx = match index {
            Index::Index(idx) => *idx,
            Index::LastIndex(idx) => length + *idx - 1,
        };
        if idx >= 0 && idx < length {
            Some(idx as usize)
        } else {
            None
        }
    }

    // check and convert slice to Array indices.
    fn convert_slice(start: &Index, end: &Index, length: i32) -> Option<Vec<usize>> {
        let start = match start {
            Index::Index(idx) => *idx,
            Index::LastIndex(idx) => length + *idx - 1,
        };
        let end = match end {
            Index::Index(idx) => *idx,
            Index::LastIndex(idx) => length + *idx - 1,
        };
        if start > end || start >= length || end < 0 {
            None
        } else {
            let start = if start < 0 { 0 } else { start as usize };
            let end = if end >= length {
                (length - 1) as usize
            } else {
                end as usize
            };
            Some((start..=end).collect())
        }
    }

    fn filter_expr(&'a self, root: &'a [u8], current: &'a [u8], expr: &Expr<'a>) -> bool {
        match expr {
            Expr::BinaryOp { op, left, right } => match op {
                BinaryOperator::Or => {
                    let lhs = self.filter_expr(root, current, left);
                    let rhs = self.filter_expr(root, current, right);
                    lhs || rhs
                }
                BinaryOperator::And => {
                    let lhs = self.filter_expr(root, current, left);
                    let rhs = self.filter_expr(root, current, right);
                    lhs && rhs
                }
                _ => {
                    let lhs = self.convert_expr_val(root, current, *left.clone());
                    let rhs = self.convert_expr_val(root, current, *right.clone());
                    self.compare(op, &lhs, &rhs)
                }
            },
            _ => todo!(),
        }
    }

    fn convert_expr_val(
        &'a self,
        root: &'a [u8],
        current: &'a [u8],
        expr: Expr<'a>,
    ) -> ExprValue<'a> {
        match expr {
            Expr::Value(value) => ExprValue::Value(value.clone()),
            Expr::Paths(paths) => {
                // get value from path and convert to `ExprValue`.
                let mut items = VecDeque::new();
                if let Some(Path::Current) = paths.get(0) {
                    items.push_back(Item::Container(current));
                } else {
                    items.push_back(Item::Container(root));
                }

                for path in paths.iter().skip(1) {
                    match path {
                        &Path::Root | &Path::Current | &Path::FilterExpr(_) => unreachable!(),
                        _ => {
                            let len = items.len();
                            for _ in 0..len {
                                let item = items.pop_front().unwrap();
                                match item {
                                    Item::Container(current) => {
                                        self.select_path(current, path, &mut items);
                                    }
                                    Item::Scalar(_) => {
                                        // In lax mode, bracket wildcard allow Scalar value.
                                        if path == &Path::BracketWildcard {
                                            items.push_back(item);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                let mut values = Vec::with_capacity(items.len());
                while let Some(item) = items.pop_front() {
                    let val = match item {
                        Item::Container(val) => val,
                        Item::Scalar(ref val) => val.as_slice(),
                    };
                    let (rest, (ty, _)) = decode_header(val).unwrap();
                    if ty == SCALAR_CONTAINER_TAG {
                        let (rest, (jty, jlength)) = decode_jentry(rest).unwrap();
                        let value = match jty {
                            NULL_TAG => PathValue::Null,
                            TRUE_TAG => PathValue::Boolean(true),
                            FALSE_TAG => PathValue::Boolean(false),
                            NUMBER_TAG => {
                                let n = Number::decode(&rest[0..jlength]);
                                PathValue::Number(n)
                            }
                            STRING_TAG => {
                                let v = &rest[0..jlength];
                                PathValue::String(Cow::Owned(unsafe {
                                    String::from_utf8_unchecked(v.to_vec())
                                }))
                            }
                            _ => unreachable!(),
                        };
                        values.push(value);
                    }
                }
                ExprValue::Values(values)
            }
            _ => unreachable!(),
        }
    }

    fn compare(&'a self, op: &BinaryOperator, lhs: &ExprValue<'a>, rhs: &ExprValue<'a>) -> bool {
        match (lhs, rhs) {
            (ExprValue::Value(lhs), ExprValue::Value(rhs)) => {
                self.compare_value(op, *lhs.clone(), *rhs.clone())
            }
            (ExprValue::Values(lhses), ExprValue::Value(rhs)) => {
                for lhs in lhses.iter() {
                    if self.compare_value(op, lhs.clone(), *rhs.clone()) {
                        return true;
                    }
                }
                false
            }
            (ExprValue::Value(lhs), ExprValue::Values(rhses)) => {
                for rhs in rhses.iter() {
                    if self.compare_value(op, *lhs.clone(), rhs.clone()) {
                        return true;
                    }
                }
                false
            }
            (ExprValue::Values(lhses), ExprValue::Values(rhses)) => {
                for lhs in lhses.iter() {
                    for rhs in rhses.iter() {
                        if self.compare_value(op, lhs.clone(), rhs.clone()) {
                            return true;
                        }
                    }
                }
                false
            }
        }
    }

    fn compare_value(
        &'a self,
        op: &BinaryOperator,
        lhs: PathValue<'a>,
        rhs: PathValue<'a>,
    ) -> bool {
        let order = lhs.partial_cmp(&rhs);
        if let Some(order) = order {
            match op {
                BinaryOperator::Eq => order == Ordering::Equal,
                BinaryOperator::NotEq => order != Ordering::Equal,
                BinaryOperator::Lt => order == Ordering::Less,
                BinaryOperator::Lte => order == Ordering::Equal || order == Ordering::Less,
                BinaryOperator::Gt => order == Ordering::Greater,
                BinaryOperator::Gte => order == Ordering::Equal || order == Ordering::Greater,
                _ => unreachable!(),
            }
        } else {
            false
        }
    }
}

fn decode_header(input: &[u8]) -> IResult<&[u8], (u32, usize)> {
    map(be_u32, |header| {
        (
            header & CONTAINER_HEADER_TYPE_MASK,
            (header & CONTAINER_HEADER_LEN_MASK) as usize,
        )
    })(input)
}

fn decode_jentry(input: &[u8]) -> IResult<&[u8], (u32, usize)> {
    map(be_u32, |jentry| {
        (
            jentry & JENTRY_TYPE_MASK,
            (jentry & JENTRY_OFF_LEN_MASK) as usize,
        )
    })(input)
}

fn decode_jentries(input: &[u8], length: usize) -> IResult<&[u8], Vec<(u32, usize)>> {
    count(decode_jentry, length)(input)
}

fn decode_string(input: &[u8], length: usize) -> IResult<&[u8], &[u8]> {
    take(length)(input)
}
