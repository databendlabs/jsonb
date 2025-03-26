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
use std::collections::VecDeque;

use crate::core::ArrayBuilder;
use crate::core::ArrayIterator;
use crate::core::JsonbItem;
use crate::core::JsonbItemType;
use crate::core::ObjectIterator;
use crate::error::Result;
use crate::jsonpath::ArrayIndex;
use crate::jsonpath::BinaryOperator;
use crate::jsonpath::Expr;
use crate::jsonpath::FilterFunc;
use crate::jsonpath::JsonPath;
use crate::jsonpath::Path;
use crate::jsonpath::PathValue;
use crate::number::Number;
use crate::Error;
use crate::OwnedJsonb;
use crate::RawJsonb;

#[derive(Debug)]
enum ExprValue<'a> {
    Values(Vec<PathValue<'a>>),
    Value(Box<PathValue<'a>>),
}

/// Mode determines the different forms of the return value.
#[derive(Clone, PartialEq, Debug)]
pub enum Mode {
    /// Only return the first jsonb value.
    First,
    /// Return all values as a jsonb Array.
    Array,
    /// Return each jsonb value separately.
    All,
    /// If there are multiple values, return a jsonb Array,
    /// if there is only one value, return the jsonb value directly.
    Mixed,
}

#[derive(Debug, Clone)]
pub(crate) struct Selector<'a> {
    root_jsonb: RawJsonb<'a>,
    items: VecDeque<JsonbItem<'a>>,
}

impl<'a> Selector<'a> {
    pub(crate) fn new(root_jsonb: RawJsonb<'a>) -> Selector<'a> {
        Self {
            root_jsonb,
            items: VecDeque::new(),
        }
    }

    pub(crate) fn execute(&mut self, json_path: &'a JsonPath<'a>) -> Result<()> {
        // add root jsonb
        let root_item = JsonbItem::Raw(self.root_jsonb);
        self.items.clear();
        self.items.push_front(root_item);

        if json_path.paths.len() == 1 {
            if let Path::Predicate(expr) = &json_path.paths[0] {
                let root_item = self.items.pop_front().unwrap();
                let res = self.filter_expr(root_item, expr)?;
                let res_item = JsonbItem::Boolean(res);
                self.items.push_back(res_item);
                return Ok(());
            }
        }
        self.select_by_paths(&json_path.paths)?;

        Ok(())
    }

    pub(crate) fn build(&mut self) -> Result<Vec<OwnedJsonb>> {
        let mut values = Vec::with_capacity(self.items.len());
        while let Some(item) = self.items.pop_front() {
            let value = OwnedJsonb::from_item(item)?;
            values.push(value);
        }
        Ok(values)
    }

    pub(crate) fn build_array(&mut self) -> Result<OwnedJsonb> {
        let mut builder = ArrayBuilder::with_capacity(self.items.len());
        while let Some(item) = self.items.pop_front() {
            builder.push_jsonb_item(item);
        }
        builder.build()
    }

    pub(crate) fn build_first(&mut self) -> Result<Option<OwnedJsonb>> {
        if let Some(item) = self.items.pop_front() {
            let value = OwnedJsonb::from_item(item)?;
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn build_value(&mut self) -> Result<Option<OwnedJsonb>> {
        if self.items.len() > 1 {
            let array = self.build_array()?;
            Ok(Some(array))
        } else {
            self.build_first()
        }
    }

    pub(crate) fn exists(&mut self, json_path: &'a JsonPath<'a>) -> Result<bool> {
        if json_path.is_predicate() {
            return Ok(true);
        }
        self.execute(json_path)?;
        Ok(!self.items.is_empty())
    }

    pub(crate) fn predicate_match(&mut self, json_path: &'a JsonPath<'a>) -> Result<bool> {
        if !json_path.is_predicate() {
            return Err(Error::InvalidJsonPathPredicate);
        }
        self.execute(json_path)?;
        if let Some(JsonbItem::Boolean(v)) = self.items.pop_front() {
            return Ok(v);
        }
        Err(Error::InvalidJsonPathPredicate)
    }

    fn select_by_paths(&mut self, paths: &'a [Path<'a>]) -> Result<()> {
        if let Some(Path::Current) = paths.first() {
            return Err(Error::InvalidJsonPath);
        }

        for path in paths.iter() {
            match path {
                &Path::Root | &Path::Current => {
                    continue;
                }
                Path::FilterExpr(expr) | Path::Predicate(expr) => {
                    let len = self.items.len();
                    for _ in 0..len {
                        let item = self.items.pop_front().unwrap();
                        let res = self.filter_expr(item.clone(), expr)?;
                        if res {
                            self.items.push_back(item);
                        }
                    }
                }
                _ => {
                    self.select_by_path(path)?;
                }
            }
        }
        Ok(())
    }

    pub(crate) fn select_by_path(&mut self, path: &'a Path<'a>) -> Result<bool> {
        if self.items.is_empty() {
            return Ok(false);
        }

        let len = self.items.len();
        for _ in 0..len {
            let item = self.items.pop_front().unwrap();

            match path {
                Path::DotWildcard => {
                    self.select_object_values(item)?;
                }
                Path::BracketWildcard => {
                    self.select_array_values(item)?;
                }
                Path::ColonField(name) | Path::DotField(name) | Path::ObjectField(name) => {
                    self.select_object_values_by_name(item, name)?;
                }
                Path::ArrayIndices(array_indices) => {
                    self.select_array_values_by_indices(item, array_indices)?;
                }
                _ => todo!(),
            }
        }
        Ok(true)
    }

    fn select_object_values(&mut self, parent_item: JsonbItem<'a>) -> Result<()> {
        let Some(curr_raw_jsonb) = parent_item.as_raw_jsonb() else {
            return Ok(());
        };

        let object_iter_opt = ObjectIterator::new(curr_raw_jsonb)?;
        if let Some(mut object_iter) = object_iter_opt {
            for result in &mut object_iter {
                let (_, val_item) = result?;
                self.items.push_back(val_item);
            }
        }
        Ok(())
    }

    fn select_object_values_by_name(
        &mut self,
        parent_item: JsonbItem<'a>,
        name: &'a str,
    ) -> Result<()> {
        let Some(curr_raw_jsonb) = parent_item.as_raw_jsonb() else {
            return Ok(());
        };

        let key_name = Cow::Borrowed(name);
        if let Some(val_item) =
            curr_raw_jsonb.get_object_value_by_key_name(&key_name, |name, key| key.eq(name))?
        {
            self.items.push_back(val_item);
        }
        Ok(())
    }

    fn select_array_values(&mut self, parent_item: JsonbItem<'a>) -> Result<()> {
        let Some(curr_raw_jsonb) = parent_item.as_raw_jsonb() else {
            // In lax mode, bracket wildcard allow Scalar and Object value.
            self.items.push_back(parent_item);
            return Ok(());
        };

        let array_iter_opt = ArrayIterator::new(curr_raw_jsonb)?;
        if let Some(mut array_iter) = array_iter_opt {
            for item_result in &mut array_iter {
                let item = item_result?;
                self.items.push_back(item);
            }
        } else {
            // In lax mode, bracket wildcard allow Scalar and Object value.
            self.items.push_back(parent_item);
        }
        Ok(())
    }

    fn select_array_values_by_indices(
        &mut self,
        parent_item: JsonbItem<'a>,
        array_indices: &Vec<ArrayIndex>,
    ) -> Result<()> {
        let Some(curr_raw_jsonb) = parent_item.as_raw_jsonb() else {
            return Ok(());
        };

        let jsonb_item_type = curr_raw_jsonb.jsonb_item_type()?;
        let JsonbItemType::Array(arr_len) = jsonb_item_type else {
            return Ok(());
        };
        for array_index in array_indices {
            let indices = array_index.to_indices(arr_len);
            if indices.is_empty() {
                continue;
            }
            let array_iter_opt = ArrayIterator::new(curr_raw_jsonb)?;
            if let Some(array_iter) = array_iter_opt {
                for (i, item_result) in &mut array_iter.enumerate() {
                    let item = item_result?;
                    if indices.contains(&i) {
                        self.items.push_back(item);
                    }
                }
            }
        }
        Ok(())
    }

    // fn filter_expr(&'a self, raw_jsonb: RawJsonb<'a>, item: JsonbItem<'a>, expr: &Expr<'a>) -> Result<bool> {
    fn filter_expr(&mut self, item: JsonbItem<'a>, expr: &'a Expr<'a>) -> Result<bool> {
        match expr {
            Expr::BinaryOp { op, left, right } => match op {
                BinaryOperator::Or => {
                    let lhs = self.filter_expr(item.clone(), left)?;
                    let rhs = self.filter_expr(item.clone(), right)?;
                    Ok(lhs || rhs)
                }
                BinaryOperator::And => {
                    let lhs = self.filter_expr(item.clone(), left)?;
                    let rhs = self.filter_expr(item.clone(), right)?;
                    Ok(lhs && rhs)
                }
                _ => {
                    let lhs = self.convert_expr_val(item.clone(), left)?;
                    let rhs = self.convert_expr_val(item.clone(), right)?;
                    let res = self.compare(op, &lhs, &rhs);
                    Ok(res)
                }
            },
            Expr::FilterFunc(filter_expr) => match filter_expr {
                FilterFunc::Exists(paths) => self.eval_exists(item, paths),
                FilterFunc::StartsWith(prefix) => self.eval_starts_with(item, prefix),
            },
            _ => todo!(),
        }
    }

    fn eval_exists(&mut self, item: JsonbItem<'a>, paths: &'a [Path<'a>]) -> Result<bool> {
        let filter_items = self.select_by_filter_paths(item, paths)?;
        let res = !filter_items.is_empty();
        Ok(res)
    }

    fn eval_starts_with(&mut self, item: JsonbItem<'a>, prefix: &str) -> Result<bool> {
        if let JsonbItem::String(data) = item {
            let val = unsafe { String::from_utf8_unchecked(data.to_vec()) };
            let res = val.starts_with(prefix);
            if res {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn select_by_filter_paths(
        &mut self,
        item: JsonbItem<'a>,
        paths: &'a [Path<'a>],
    ) -> Result<VecDeque<JsonbItem<'a>>> {
        let mut items = VecDeque::new();
        if let Some(Path::Current) = paths.first() {
            items.push_front(item.clone());
        } else {
            let root_item = JsonbItem::Raw(self.root_jsonb);
            items.push_front(root_item);
        }
        std::mem::swap(&mut self.items, &mut items);

        for path in paths.iter() {
            match path {
                &Path::Root | &Path::Current => {
                    continue;
                }
                Path::FilterExpr(expr) | Path::Predicate(expr) => {
                    let len = self.items.len();
                    for _ in 0..len {
                        let item = self.items.pop_front().unwrap();
                        let res = self.filter_expr(item.clone(), expr)?;
                        if res {
                            self.items.push_back(item);
                        }
                    }
                }
                _ => {
                    self.select_by_path(path)?;
                }
            }
        }
        std::mem::swap(&mut self.items, &mut items);
        Ok(items)
    }

    fn convert_expr_val(
        &mut self,
        item: JsonbItem<'a>,
        expr: &'a Expr<'a>,
    ) -> Result<ExprValue<'a>> {
        match expr {
            Expr::Value(value) => Ok(ExprValue::Value(value.clone())),
            Expr::Paths(paths) => {
                let mut filter_items = self.select_by_filter_paths(item, paths)?;

                let mut values = Vec::with_capacity(filter_items.len());
                while let Some(item) = filter_items.pop_front() {
                    let value = match item {
                        JsonbItem::Null => PathValue::Null,
                        JsonbItem::Boolean(v) => PathValue::Boolean(v),
                        JsonbItem::Number(data) => {
                            let n = Number::decode(data)?;
                            PathValue::Number(n)
                        }
                        JsonbItem::String(data) => PathValue::String(Cow::Owned(unsafe {
                            String::from_utf8_unchecked(data.to_vec())
                        })),
                        _ => {
                            continue;
                        }
                    };
                    values.push(value);
                }
                Ok(ExprValue::Values(values))
            }
            _ => unreachable!(),
        }
    }

    fn compare(&mut self, op: &BinaryOperator, lhs: &ExprValue<'a>, rhs: &ExprValue<'a>) -> bool {
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
        &mut self,
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
