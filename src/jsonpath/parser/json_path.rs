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

use nom::combinator::map;

use crate::jsonpath::ast::*;
use crate::jsonpath::input::Input;
use crate::jsonpath::parser::expr::*;
use crate::jsonpath::parser::token::*;
//use crate::jsonpath::rule;
use crate::rule;

use crate::jsonpath::util::*;

pub fn path(i: Input) -> IResult<Path> {
    let root = map(
        rule! {
            Dollar
        },
        |_| Path::Root,
    );
    let current = map(
        rule! {
            AtSign
        },
        |_| Path::Current,
    );
    let dot_wildcard = map(
        rule! {
            Period ~ Multiply
        },
        |(_, _)| Path::DotWildcard,
    );
    let descent_wildcard = map(
        rule! {
            DoublePeriod ~ Multiply
        },
        |(_, _)| Path::DescentWildcard,
    );
    let bracket_wildcard = map(
        rule! {
            LBracket ~ Multiply ~ RBracket
        },
        |(_, _, _)| Path::BracketWildcard,
    );
    let dot_field = map(
        rule! {
            Period ~ #ident
        },
        |(_, field)| Path::DotField(field.to_string()),
    );
    let descent_field = map(
        rule! {
            DoublePeriod ~ #ident
        },
        |(_, field)| Path::DescentField(field.to_string()),
    );
    let object_fields = map(
        rule! { "[" ~ #comma_separated_list1(literal_string) ~ "]" },
        |(_, fields, _)| Path::ObjectFields(fields),
    );
    let array_indices = map(
        rule! { "[" ~ #comma_separated_list1(literal_i64) ~ "]" },
        |(_, indices, _)| Path::ArrayIndices(indices),
    );
    let array_slice = map(
        rule! {
            "[" ~ #literal_i64? ~ Colon ~ #literal_i64? ~ ( Colon ~ #literal_i64 )? ~ "]"
        },
        |(_, opt_start, _, opt_end, opt_step, _)| Path::ArraySlice {
            start: opt_start,
            end: opt_end,
            step: opt_step.map(|(_, step)| step),
        },
    );

    rule!(
        #root: "`$`"
        | #current: "`@`"
        | #dot_wildcard: "`.*`"
        | #descent_wildcard: "`..*`"
        | #bracket_wildcard: "`[*]`"
        | #dot_field: "`.field`"
        | #descent_field: "`..field`"
        | #object_fields: "`[\"field1\",\"field2\"]`"
        | #array_indices: "`[0,1,2]`"
        | #array_slice: "`[start:end:step]`"
    )(i)
}

pub fn json_path(i: Input) -> IResult<JsonPath> {
    let json_path = map(
        rule! {
            #continue_list1(path_item) ~ &EOI
        },
        |(items, _)| JsonPath { items },
    );

    rule!(
        #json_path: "`<json_path>`"
    )(i)
}

pub fn path_item(i: Input) -> IResult<PathItem> {
    let path = map(rule! { #path }, |path| PathItem::Path {
        path: Box::new(path),
    });
    let filter_expr = map(
        rule! {
            "[" ~ Placeholder ~ "(" ~ #subexpr(0) ~ ")" ~ "]"
        },
        |(_, _, _, expr, _, _)| PathItem::FilterExpr {
            expr: Box::new(expr),
        },
    );

    rule!(
        #path: "`<path>`"
        | #filter_expr: "`[?(<expression>)]`"
    )(i)
}
