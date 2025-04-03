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
use crate::core::ObjectValueIterator;
use crate::error::Result;
use crate::jsonpath::ArithmeticFunc;
use crate::jsonpath::ArrayIndex;
use crate::jsonpath::BinaryArithmeticOperator;
use crate::jsonpath::BinaryOperator;
use crate::jsonpath::Expr;
use crate::jsonpath::JsonPath;
use crate::jsonpath::Path;
use crate::jsonpath::PathValue;
use crate::jsonpath::RecursiveLevel;
use crate::jsonpath::UnaryArithmeticOperator;
use crate::number::Number;
use crate::to_owned_jsonb;
use crate::Error;
use crate::OwnedJsonb;
use crate::RawJsonb;

#[derive(Debug)]
enum ExprValue<'a> {
    Values(Vec<PathValue<'a>>),
    Value(Box<PathValue<'a>>),
}

impl ExprValue<'_> {
    fn convert_to_number(self) -> Result<Number> {
        match self {
            ExprValue::Values(mut vals) => {
                if vals.len() != 1 {
                    return Err(Error::InvalidJsonPath);
                }
                let val = vals.pop().unwrap();
                match val {
                    PathValue::Number(num) => Ok(num),
                    _ => Err(Error::InvalidJsonPath),
                }
            }
            ExprValue::Value(val) => match *val {
                PathValue::Number(num) => Ok(num),
                _ => Err(Error::InvalidJsonPath),
            },
        }
    }

    fn convert_to_numbers(self) -> Result<Vec<Number>> {
        match self {
            ExprValue::Values(vals) => {
                let mut nums = Vec::with_capacity(vals.len());
                for val in vals {
                    if let PathValue::Number(num) = val {
                        nums.push(num);
                    } else {
                        return Err(Error::InvalidJsonPath);
                    }
                }
                Ok(nums)
            }
            ExprValue::Value(val) => match *val {
                PathValue::Number(num) => Ok(vec![num]),
                _ => Err(Error::InvalidJsonPath),
            },
        }
    }
}

/// Represents the state of a JSON Path selection process.
///
/// It holds the root JSONB value and the intermediate results (items) found during
/// the execution of a `JsonPath`.
pub struct Selector<'a> {
    /// The root JSONB value against which the path is executed.
    root_jsonb: RawJsonb<'a>,
    /// A queue holding the JSONB items that match the path criteria during execution.
    items: VecDeque<JsonbItem<'a>>,
}

impl<'a> Selector<'a> {
    /// Creates a new `Selector` for the given root `RawJsonb`.
    ///
    /// # Arguments
    ///
    /// * `root_jsonb` - The `RawJsonb` data to select from.
    pub fn new(root_jsonb: RawJsonb<'a>) -> Selector<'a> {
        Self {
            root_jsonb,
            items: VecDeque::new(),
        }
    }

    /// Executes the `JsonPath` and collects all matching items into a `Vec<OwnedJsonb>`.
    ///
    /// This function returns all matching elements as a `Vec<OwnedJsonb>`.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONPath selector.
    /// * `json_path` - The JSONPath expression.
    ///
    /// # Returns
    ///
    /// * `Ok(Vec<OwnedJsonb>)` - A vector containing the selected `OwnedJsonb` values.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation.
    ///
    /// # Examples
    ///
    /// ```
    /// use jsonb::jsonpath::parse_json_path;
    /// use jsonb::jsonpath::Selector;
    /// use jsonb::OwnedJsonb;
    ///
    /// let jsonb_value = r#"{"a": {"b": [1, 2, 3]}, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let mut selector = Selector::new(raw_jsonb);
    ///
    /// let path = parse_json_path("$.a.b[*]".as_bytes()).unwrap();
    /// let result = selector.select_values(&path).unwrap();
    /// assert_eq!(result.len(), 3);
    /// assert_eq!(result[0].to_string(), "1");
    /// assert_eq!(result[1].to_string(), "2");
    /// assert_eq!(result[2].to_string(), "3");
    /// ```
    ///
    /// # See Also
    ///
    /// * `RawJsonb::select_by_path`.
    pub fn select_values(&mut self, json_path: &'a JsonPath<'a>) -> Result<Vec<OwnedJsonb>> {
        self.execute(json_path)?;
        let mut values = Vec::with_capacity(self.items.len());
        while let Some(item) = self.items.pop_front() {
            let value = OwnedJsonb::from_item(item)?;
            values.push(value);
        }
        Ok(values)
    }

    /// Executes the `JsonPath` and builds a JSON array `OwnedJsonb` from all matching items.
    ///
    /// This function returns all matching elements as a single `OwnedJsonb` representing a JSON array.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONPath selector.
    /// * `json_path` - The JSONPath expression.
    ///
    /// # Returns
    ///
    /// * `Ok(OwnedJsonb)` - A single `OwnedJsonb` (a JSON array) containing the selected values.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation.
    ///
    /// # Examples
    ///
    /// ```
    /// use jsonb::jsonpath::parse_json_path;
    /// use jsonb::jsonpath::Selector;
    /// use jsonb::OwnedJsonb;
    ///
    /// let jsonb_value = r#"{"a": {"b": [1, 2, 3]}, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let mut selector = Selector::new(raw_jsonb);
    ///
    /// let path = parse_json_path("$.a.b[*]".as_bytes()).unwrap();
    /// let result = selector.select_array(&path).unwrap();
    /// assert_eq!(result.to_string(), "[1,2,3]");
    /// ```
    ///
    /// # See Also
    ///
    /// * `RawJsonb::select_array_by_path`.
    pub fn select_array(&mut self, json_path: &'a JsonPath<'a>) -> Result<OwnedJsonb> {
        self.execute(json_path)?;
        let mut builder = ArrayBuilder::with_capacity(self.items.len());
        while let Some(item) = self.items.pop_front() {
            builder.push_jsonb_item(item);
        }
        builder.build()
    }

    /// Executes the `JsonPath` and returns the first matching item as an `Option<OwnedJsonb>`.
    ///
    /// This function returns the first matched element wrapped in `Some`, or `None` if no element matches the path.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONPath selector.
    /// * `json_path` - The JSONPath expression.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(OwnedJsonb))` - A single `OwnedJsonb` containing the first matched value.
    /// * `Ok(None)` - The path does not match any values.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::jsonpath::parse_json_path;
    /// use jsonb::jsonpath::Selector;
    /// use jsonb::OwnedJsonb;
    ///
    /// let jsonb_value = r#"{"a": [{"b": 1}, {"b": 2}], "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let mut selector = Selector::new(raw_jsonb);
    ///
    /// let path = parse_json_path("$.a[0].b".as_bytes()).unwrap(); // Matches multiple values.
    /// let result = selector.select_first(&path).unwrap();
    /// assert_eq!(result.unwrap().to_string(), "1");
    ///
    /// let path = parse_json_path("$.d".as_bytes()).unwrap(); // No match.
    /// let result = selector.select_first(&path).unwrap();
    /// assert!(result.is_none());
    /// ```
    ///
    /// # See Also
    ///
    /// * `RawJsonb::select_first_by_path`.
    pub fn select_first(&mut self, json_path: &'a JsonPath<'a>) -> Result<Option<OwnedJsonb>> {
        self.execute(json_path)?;
        if let Some(item) = self.items.pop_front() {
            let value = OwnedJsonb::from_item(item)?;
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }

    /// Executes the `JsonPath` and returns a single value or an array of values.
    ///
    /// If exactly one element matches, it is returned directly (wrapped in `Some`).
    /// If multiple elements match, they are returned as a JSON array (wrapped in `Some`).
    /// If no elements match, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONPath selector.
    /// * `json_path` - The JSONPath expression.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(OwnedJsonb))` - A single `OwnedJsonb` containing the matched values.
    /// * `Ok(None)` - The path does not match any values.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::jsonpath::parse_json_path;
    /// use jsonb::jsonpath::Selector;
    /// use jsonb::OwnedJsonb;
    ///
    /// let jsonb_value = r#"{"a": [{"b": 1}, {"b": 2}], "c": 3}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let mut selector = Selector::new(raw_jsonb);
    ///
    /// let path = parse_json_path("$.c".as_bytes()).unwrap(); // Matches a single value.
    /// let result = selector.select_value(&path).unwrap();
    /// assert_eq!(result.unwrap().to_string(), "3");
    ///
    /// let path = parse_json_path("$.a[*].b".as_bytes()).unwrap(); // Matches multiple values.
    /// let result = selector.select_value(&path).unwrap();
    /// assert_eq!(result.unwrap().to_string(), "[1,2]");
    ///
    /// let path = parse_json_path("$.x".as_bytes()).unwrap(); // No match.
    /// let result = selector.select_value(&path).unwrap();
    /// assert!(result.is_none());
    /// ```
    ///
    /// # See Also
    ///
    /// * `RawJsonb::select_value_by_path`.
    pub fn select_value(&mut self, json_path: &'a JsonPath<'a>) -> Result<Option<OwnedJsonb>> {
        self.execute(json_path)?;
        if self.items.len() > 1 {
            let mut builder = ArrayBuilder::with_capacity(self.items.len());
            while let Some(item) = self.items.pop_front() {
                builder.push_jsonb_item(item);
            }
            let array = builder.build()?;
            Ok(Some(array))
        } else if let Some(item) = self.items.pop_front() {
            let value = OwnedJsonb::from_item(item)?;
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }

    /// Executes the `JsonPath` and checks if any item matches.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONPath selector.
    /// * `json_path` - The JSONPath expression.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the JSON path exists.
    /// * `Ok(false)` - If the JSON path does not exist.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation.
    ///   This could also indicate issues with the `json_path` itself.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::jsonpath::parse_json_path;
    /// use jsonb::jsonpath::Selector;
    /// use jsonb::OwnedJsonb;
    ///
    /// let jsonb_value = r#"{"a": {"b": [1, 2, 3]}, "c": 4}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let mut selector = Selector::new(raw_jsonb);
    ///
    /// // Valid paths
    /// let path1 = parse_json_path("$.a.b[1]".as_bytes()).unwrap();
    /// assert!(selector.exists(&path1).unwrap());
    ///
    /// let path2 = parse_json_path("$.c".as_bytes()).unwrap();
    /// assert!(selector.exists(&path2).unwrap());
    ///
    /// // Invalid paths
    /// let path3 = parse_json_path("$.a.x".as_bytes()).unwrap(); // "x" does not exist
    /// assert!(!selector.exists(&path3).unwrap());
    /// ```
    ///
    /// # See Also
    ///
    /// * `RawJsonb::path_exists`.
    pub fn exists(&mut self, json_path: &'a JsonPath<'a>) -> Result<bool> {
        if json_path.is_predicate() {
            return Ok(true);
        }
        self.execute(json_path)?;
        Ok(!self.items.is_empty())
    }

    /// Executes a `JsonPath` predicate and returns the boolean result.
    ///
    /// This function requires that the `JsonPath` represents a predicate expression
    /// (e.g., `$.c > 1`, `exists($.a)`). It executes the path and expects a single
    /// boolean `JsonbItem` as the result.
    ///
    /// # Arguments
    ///
    /// * `self` - The JSONPath selector.
    /// * `json_path` - The JSONPath expression.
    ///
    /// # Returns
    ///
    /// * `Ok(true)` - If the JSON path with its predicate matches at least one value in the JSONB data.
    /// * `Ok(false)` - If the JSON path with its predicate does not match any values.
    /// * `Err(Error)` - If the JSONB data is invalid or if an error occurs during path evaluation or predicate checking.
    ///   This could also indicate issues with the `json_path` itself (invalid syntax, etc.).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::jsonpath::parse_json_path;
    /// use jsonb::jsonpath::Selector;
    /// use jsonb::OwnedJsonb;
    ///
    /// let jsonb_value = r#"[
    ///     {"price": 12, "title": "Book A"},
    ///     {"price": 8, "title": "Book B"},
    ///     {"price": 5, "title": "Book C"}
    /// ]"#
    /// .parse::<OwnedJsonb>()
    /// .unwrap();
    /// let raw_jsonb = jsonb_value.as_raw();
    /// let mut selector = Selector::new(raw_jsonb);
    ///
    /// // Path with predicate (select books with price < 10)
    /// let path = parse_json_path("$[*].price < 10".as_bytes()).unwrap();
    /// assert!(selector.predicate_match(&path).unwrap()); // True because Book B and Book C match.
    ///
    /// // Path with predicate (select books with title "Book D")
    /// let path = parse_json_path("$[*].title == \"Book D\"".as_bytes()).unwrap();
    /// assert!(!selector.predicate_match(&path).unwrap()); // False because no book has this title.
    /// ```
    ///
    /// # See Also
    ///
    /// * `RawJsonb::path_match`.
    pub fn predicate_match(&mut self, json_path: &'a JsonPath<'a>) -> Result<bool> {
        if !json_path.is_predicate() {
            return Err(Error::InvalidJsonPathPredicate);
        }
        self.execute(json_path)?;
        if let Some(JsonbItem::Boolean(v)) = self.items.pop_front() {
            return Ok(v);
        }
        Err(Error::InvalidJsonPathPredicate)
    }

    fn execute(&mut self, json_path: &'a JsonPath<'a>) -> Result<()> {
        // add root jsonb
        let root_item = JsonbItem::Raw(self.root_jsonb);
        self.items.clear();
        self.items.push_front(root_item);

        if json_path.paths.len() == 1 {
            if let Path::Expr(expr) = &json_path.paths[0] {
                let root_item = self.items.pop_front().unwrap();
                self.eval_expr(root_item, expr)?;
                return Ok(());
            }
        }
        self.select_by_paths(&json_path.paths)?;

        Ok(())
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
                Path::FilterExpr(expr) | Path::Expr(expr) => {
                    let len = self.items.len();
                    for _ in 0..len {
                        let item = self.items.pop_front().unwrap();
                        let res = self.eval_filter_expr(item.clone(), expr)?.unwrap_or(false);
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

    fn select_by_path(&mut self, path: &'a Path<'a>) -> Result<bool> {
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
                Path::RecursiveDotWildcard(index_opt) => {
                    self.recursive_select_values(item, 0, index_opt)?;
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

        let object_val_iter_opt = ObjectValueIterator::new(curr_raw_jsonb)?;
        if let Some(mut object_val_iter) = object_val_iter_opt {
            for result in &mut object_val_iter {
                let val_item = result?;
                self.items.push_back(val_item);
            }
        }
        Ok(())
    }

    fn recursive_select_values(
        &mut self,
        parent_item: JsonbItem<'a>,
        curr_level: u8,
        recursive_level_opt: &Option<RecursiveLevel>,
    ) -> Result<()> {
        let (is_match, should_continue) = if let Some(recursive_level) = recursive_level_opt {
            recursive_level.check_recursive_level(curr_level)
        } else {
            (true, true)
        };
        if is_match {
            self.items.push_back(parent_item.clone());
        }
        let Some(curr_raw_jsonb) = parent_item.as_raw_jsonb() else {
            return Ok(());
        };
        if !should_continue {
            return Ok(());
        }
        let object_val_iter_opt = ObjectValueIterator::new(curr_raw_jsonb)?;
        if let Some(mut object_val_iter) = object_val_iter_opt {
            for result in &mut object_val_iter {
                let val_item = result?;
                self.recursive_select_values(val_item, curr_level + 1, recursive_level_opt)?;
            }
        }
        let array_iter_opt = ArrayIterator::new(curr_raw_jsonb)?;
        if let Some(mut array_iter) = array_iter_opt {
            for item_result in &mut array_iter {
                let item = item_result?;
                self.recursive_select_values(item, curr_level + 1, recursive_level_opt)?;
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

    fn eval_expr(&mut self, item: JsonbItem<'a>, expr: &'a Expr<'a>) -> Result<()> {
        match expr {
            Expr::ArithmeticFunc(func) => {
                let res_items = self.eval_arithmetic_func(item.clone(), func)?;
                for res_item in res_items {
                    self.items.push_back(res_item);
                }
            }
            Expr::BinaryOp { .. } | Expr::ExistsFunc(_) => {
                let res = self.eval_filter_expr(item, expr)?;
                let res_item = if let Some(res) = res {
                    JsonbItem::Boolean(res)
                } else {
                    JsonbItem::Null
                };
                self.items.push_back(res_item);
            }
            Expr::Value(val) => {
                let res_item = self.eval_value(val)?;
                self.items.push_back(res_item);
            }
            Expr::Paths(_) => {
                return Err(Error::InvalidJsonPath);
            }
        }
        Ok(())
    }

    fn eval_arithmetic_func(
        &mut self,
        item: JsonbItem<'a>,
        func: &'a ArithmeticFunc<'a>,
    ) -> Result<Vec<JsonbItem<'a>>> {
        match func {
            ArithmeticFunc::Unary { op, operand } => {
                let operand = self.convert_expr_val(item.clone(), operand)?;
                let Ok(nums) = operand.convert_to_numbers() else {
                    return Err(Error::InvalidJsonPath);
                };
                let mut num_vals = Vec::with_capacity(nums.len());
                match op {
                    UnaryArithmeticOperator::Add => {
                        for num in nums {
                            let owned_num = to_owned_jsonb(&num)?;
                            num_vals.push(JsonbItem::Owned(owned_num));
                        }
                    }
                    UnaryArithmeticOperator::Subtract => {
                        for num in nums {
                            let neg_num = num.neg()?;
                            let owned_num = to_owned_jsonb(&neg_num)?;
                            num_vals.push(JsonbItem::Owned(owned_num));
                        }
                    }
                };
                Ok(num_vals)
            }
            ArithmeticFunc::Binary { op, left, right } => {
                let lhs = self.convert_expr_val(item.clone(), left)?;
                let rhs = self.convert_expr_val(item.clone(), right)?;
                let Ok(lnum) = lhs.convert_to_number() else {
                    return Err(Error::InvalidJsonPath);
                };
                let Ok(rnum) = rhs.convert_to_number() else {
                    return Err(Error::InvalidJsonPath);
                };

                let num_val = match op {
                    BinaryArithmeticOperator::Add => lnum.add(rnum)?,
                    BinaryArithmeticOperator::Subtract => lnum.sub(rnum)?,
                    BinaryArithmeticOperator::Multiply => lnum.mul(rnum)?,
                    BinaryArithmeticOperator::Divide => lnum.div(rnum)?,
                    BinaryArithmeticOperator::Modulo => lnum.rem(rnum)?,
                };
                let owned_num = to_owned_jsonb(&num_val)?;
                Ok(vec![JsonbItem::Owned(owned_num)])
            }
        }
    }

    fn eval_value(&mut self, val: &PathValue<'a>) -> Result<JsonbItem<'a>> {
        let owned_val = match val {
            PathValue::Null => to_owned_jsonb(&vec![&()])?,
            PathValue::Boolean(v) => to_owned_jsonb(&vec![v])?,
            PathValue::Number(v) => to_owned_jsonb(&vec![v])?,
            PathValue::String(v) => to_owned_jsonb(&vec![v.to_string()])?,
            PathValue::Raw(v) => {
                return Ok(JsonbItem::Raw(*v));
            }
        };
        Ok(JsonbItem::Owned(owned_val))
    }

    fn eval_filter_expr(
        &mut self,
        item: JsonbItem<'a>,
        expr: &'a Expr<'a>,
    ) -> Result<Option<bool>> {
        match expr {
            Expr::BinaryOp { op, left, right } => match op {
                BinaryOperator::Or => {
                    let lhs = self.eval_filter_expr(item.clone(), left)?;
                    let rhs = self.eval_filter_expr(item.clone(), right)?;
                    match (lhs, rhs) {
                        (Some(lhs), Some(rhs)) => Ok(Some(lhs || rhs)),
                        (_, _) => Ok(None),
                    }
                }
                BinaryOperator::And => {
                    let lhs = self.eval_filter_expr(item.clone(), left)?;
                    let rhs = self.eval_filter_expr(item.clone(), right)?;
                    match (lhs, rhs) {
                        (Some(lhs), Some(rhs)) => Ok(Some(lhs && rhs)),
                        (_, _) => Ok(None),
                    }
                }
                _ => {
                    let lhs = self.convert_expr_val(item.clone(), left)?;
                    let rhs = self.convert_expr_val(item.clone(), right)?;
                    let res = self.eval_compare(op, &lhs, &rhs);
                    Ok(res)
                }
            },
            Expr::ExistsFunc(paths) => {
                let res = self.eval_exists(item, paths)?;
                Ok(Some(res))
            }
            _ => Err(Error::InvalidJsonPath),
        }
    }

    fn eval_exists(&mut self, item: JsonbItem<'a>, paths: &'a [Path<'a>]) -> Result<bool> {
        let filter_items = self.select_by_filter_paths(item, paths)?;
        let res = !filter_items.is_empty();
        Ok(res)
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
                Path::FilterExpr(expr) => {
                    let len = self.items.len();
                    for _ in 0..len {
                        let item = self.items.pop_front().unwrap();
                        let res = self.eval_filter_expr(item.clone(), expr)?.unwrap_or(false);
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
                        JsonbItem::String(data) => PathValue::String(Cow::Borrowed(unsafe {
                            std::str::from_utf8_unchecked(data)
                        })),
                        JsonbItem::Raw(raw) => {
                            // collect values in the array.
                            let array_iter_opt = ArrayIterator::new(raw)?;
                            if let Some(mut array_iter) = array_iter_opt {
                                for item_result in &mut array_iter {
                                    let item = item_result?;
                                    let value = match item {
                                        JsonbItem::Null => PathValue::Null,
                                        JsonbItem::Boolean(v) => PathValue::Boolean(v),
                                        JsonbItem::Number(data) => {
                                            let n = Number::decode(data)?;
                                            PathValue::Number(n)
                                        }
                                        JsonbItem::String(data) => {
                                            PathValue::String(Cow::Borrowed(unsafe {
                                                std::str::from_utf8_unchecked(data)
                                            }))
                                        }
                                        JsonbItem::Raw(raw) => PathValue::Raw(raw),
                                        _ => {
                                            continue;
                                        }
                                    };
                                    values.push(value);
                                }
                            } else {
                                values.push(PathValue::Raw(raw));
                            }
                            continue;
                        }
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

    fn eval_compare(
        &mut self,
        op: &BinaryOperator,
        lhs: &ExprValue<'a>,
        rhs: &ExprValue<'a>,
    ) -> Option<bool> {
        let (lvals, rvals) = match (lhs, rhs) {
            (ExprValue::Value(lhs), ExprValue::Value(rhs)) => {
                (vec![*lhs.clone()], vec![*rhs.clone()])
            }
            (ExprValue::Values(lhses), ExprValue::Value(rhs)) => {
                (lhses.clone(), vec![*rhs.clone()])
            }
            (ExprValue::Value(lhs), ExprValue::Values(rhses)) => {
                (vec![*lhs.clone()], rhses.clone())
            }
            (ExprValue::Values(lhses), ExprValue::Values(rhses)) => (lhses.clone(), rhses.clone()),
        };

        for lval in lvals.iter() {
            for rval in rvals.iter() {
                if let Some(res) = self.compare_value(op, lval.clone(), rval.clone()) {
                    if res {
                        return Some(true);
                    }
                } else {
                    return None;
                }
            }
        }
        Some(false)
    }

    fn compare_value(
        &mut self,
        op: &BinaryOperator,
        lhs: PathValue<'a>,
        rhs: PathValue<'a>,
    ) -> Option<bool> {
        // container value can't compare values.
        if matches!(lhs, PathValue::Raw(_)) || matches!(rhs, PathValue::Raw(_)) {
            return None;
        }
        if op == &BinaryOperator::StartsWith {
            let res = match (lhs, rhs) {
                (PathValue::String(lhs), PathValue::String(rhs)) => Some(lhs.starts_with(&*rhs)),
                (_, _) => None,
            };
            return res;
        }
        let order = lhs.partial_cmp(&rhs);
        if let Some(order) = order {
            let res = match op {
                BinaryOperator::Eq => order == Ordering::Equal,
                BinaryOperator::NotEq => order != Ordering::Equal,
                BinaryOperator::Lt => order == Ordering::Less,
                BinaryOperator::Lte => order == Ordering::Equal || order == Ordering::Less,
                BinaryOperator::Gt => order == Ordering::Greater,
                BinaryOperator::Gte => order == Ordering::Equal || order == Ordering::Greater,
                _ => unreachable!(),
            };
            Some(res)
        } else {
            None
        }
    }
}
