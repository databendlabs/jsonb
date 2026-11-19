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

//! JSONPath limits: nesting and operator limits in the parser, and the work
//! and copy budgets of evaluation.

use jsonb::jsonpath::parse_json_path;
use jsonb::keypath::parse_key_paths;
use jsonb::*;

use crate::util::{nested_arrays, with_big_stack, within_timeout};

/// Parenthesis nesting limit for JSONPath (`MAX_JSON_PATH_DEPTH` in the crate).
const MAX_PATH_DEPTH: usize = 64;
/// `&&` and `||` limit for JSONPath (`MAX_JSON_PATH_LOGICAL_OPERATORS` in the crate).
const MAX_PATH_LOGICAL_OPERATORS: usize = 256;

#[test]
fn json_path_rejects_unterminated_string() {
    for path in [r#"""#, r#""a"#, r#"$."a"#, r#"$["a"#] {
        assert!(parse_json_path(path.as_bytes()).is_err(), "{path}");
        assert!(parse_key_paths(path.as_bytes()).is_err(), "{path}");
    }
}

#[test]
fn json_path_enforces_paren_limit() {
    let path = |depth: usize| {
        let inner = depth - 1;
        format!("$ ? ({}@ == 1{})", "(".repeat(inner), ")".repeat(inner))
    };
    with_big_stack(move || {
        assert!(parse_json_path(path(MAX_PATH_DEPTH).as_bytes()).is_ok());
    });
    for depth in [MAX_PATH_DEPTH + 1, 100_000] {
        assert_eq!(
            parse_json_path(path(depth).as_bytes()).err(),
            Some(Error::RecursionLimitExceeded),
            "depth {depth}"
        );
    }
    // Parentheses inside string literals do not count.
    let quoted = format!(r#"$ ? (@ == "{}")"#, "(".repeat(1000));
    assert!(parse_json_path(quoted.as_bytes()).is_ok());
}

#[test]
fn json_path_enforces_logical_operator_limit() {
    // `&&` and `||` chains parse without recursion but build a left-nested
    // tree as deep as the chain, which formatting, evaluation, cloning,
    // comparison and dropping walk recursively. 100000 operators used to
    // overflow the stack in all of them (found in review). The limit runs on
    // the test thread's default stack, without `with_big_stack`.
    //
    // `&` does not end an unquoted field name, so `a&&a` is one name. The
    // limit used to be counted by scanning the text, which rejected names
    // with more than 256 `&&`, and broke `Display` round-trips of quoted ones
    // because `Display` writes them unquoted (found in review).
    let doc: OwnedJsonb = r#"{"a&&a": 1}"#.parse().unwrap();
    let path = parse_json_path(b"$.a&&a").unwrap();
    assert_eq!(doc.as_raw().select_by_path(&path).unwrap().len(), 1);
    let name = format!("{}a", "a&&".repeat(1000));
    for text in [format!("$.{name}"), format!(r#"$."{name}""#)] {
        let path = parse_json_path(text.as_bytes()).unwrap();
        let formatted = path.to_string();
        assert_eq!(parse_json_path(formatted.as_bytes()).unwrap(), path);
    }

    // Each form has exactly `k` operators. The parser backtracks over some of
    // them, for example trying a root expression before a plain path, so a
    // chain can be parsed more than once; each operator must count once.
    fn chain(k: usize, op: &str) -> String {
        vec!["@ == 0"; k + 1].join(&format!(" {op} "))
    }
    /// A name and a function that writes the form with `k` operators.
    type Form = (&'static str, fn(usize) -> String);
    let forms: [Form; 8] = [
        ("filter with ||", |k| format!("$ ? ({})", chain(k, "||"))),
        ("filter with &&", |k| format!("$ ? ({})", chain(k, "&&"))),
        ("filter after a step", |k| {
            format!("$.a ? ({})", chain(k, "||"))
        }),
        ("filter on items", |k| {
            format!("$.a[*] ? ({})", chain(k, "&&"))
        }),
        ("root expression", |k| {
            vec!["$.a[0] == 0"; k + 1].join(" || ")
        }),
        ("mixed && and ||", |k| {
            let mut text = String::from("$ ? (@ == 0");
            for i in 0..k {
                text.push_str(if i % 2 == 0 {
                    " && @ == 0"
                } else {
                    " || @ == 0"
                });
            }
            text + ")"
        }),
        ("split by parentheses", |k| {
            let left = k / 2;
            let right = k - left - 1;
            format!("$ ? (({}) && ({}))", chain(left, "||"), chain(right, "||"))
        }),
        ("split by a nested filter", |k| {
            let inner = k / 2;
            let outer = k - inner - 1;
            format!(
                "$ ? (exists(@ ? ({})) || {})",
                chain(inner, "||"),
                chain(outer, "||")
            )
        }),
    ];
    let doc: OwnedJsonb = r#"{"a": [0, 1]}"#.parse().unwrap();
    for (form, path) in forms {
        let text = path(MAX_PATH_LOGICAL_OPERATORS);
        let parsed = parse_json_path(text.as_bytes()).unwrap_or_else(|e| panic!("{form}: {e:?}"));
        let formatted = parsed.to_string();
        assert_eq!(
            parse_json_path(formatted.as_bytes()).as_ref(),
            Ok(&parsed),
            "{form}: round-trip"
        );
        assert!(doc.as_raw().select_by_path(&parsed).is_ok(), "{form}");
        for operators in [MAX_PATH_LOGICAL_OPERATORS + 1, 100_000] {
            assert_eq!(
                parse_json_path(path(operators).as_bytes()).err(),
                Some(Error::RecursionLimitExceeded),
                "{form} with {operators} operators"
            );
        }
    }
    // Operators inside string literals do not count.
    let quoted = format!(r#"$ ? (@ == "{}")"#, "||&&".repeat(1000));
    assert!(parse_json_path(quoted.as_bytes()).is_ok());
}

#[test]
fn recursive_descent_reaches_levels_beyond_255() {
    with_big_stack(|| {
        // Levels are `u8`, so an open `to last` range is the only way to match
        // past level 255; the innermost `[]` of 300 nested arrays is level 299.
        let deep = nested_arrays(300);
        let path = parse_json_path(b"$.**{255 to last}").unwrap();
        let selected = deep.as_raw().select_by_path(&path).unwrap();
        assert_eq!(selected.len(), 300 - 255);
        assert_eq!(selected.last().unwrap().to_string(), "[]");
    });
}

#[test]
fn json_path_slices_outside_the_array_select_nothing() {
    // These used to loop over `0..=usize::MAX` after an end index underflowed.
    let array = "[1,2]".parse::<OwnedJsonb>().unwrap();
    let empty = "[]".parse::<OwnedJsonb>().unwrap();
    for (doc, path) in [
        (&array, "$[0 to last - 5]"),
        (&empty, "$[0 to 3]"),
        (&array, "$[5 to 9]"),
    ] {
        let path = parse_json_path(path.as_bytes()).unwrap();
        assert!(doc.as_raw().select_by_path(&path).unwrap().is_empty());
    }
    let path = parse_json_path(b"$[1 to 9]").unwrap();
    let selected = array.as_raw().select_by_path(&path).unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].to_string(), "2");
}

#[test]
fn path_display_round_trips_special_names() {
    // Names that need quoting or escaping when shown. The parsers reject empty
    // quoted names, so `""` is not included.
    for name in [r#"st"ore"#, "a b", "a.b", "a\\b", "$x", "1st", "tab\there"] {
        let quoted = serde_json::to_string(name).unwrap();
        for text in [
            format!("$.{quoted}"),
            format!("$[{quoted}]"),
            format!("$:{quoted}"),
            format!("a:{quoted}"),
        ] {
            let path = parse_json_path(text.as_bytes()).unwrap();
            let shown = path.to_string();
            assert_eq!(
                parse_json_path(shown.as_bytes()).unwrap(),
                path,
                "{text} shown as {shown}"
            );
        }
        let text = format!("{{{quoted},0}}");
        let key_paths = parse_key_paths(text.as_bytes()).unwrap();
        let shown = key_paths.to_string();
        assert_eq!(
            parse_key_paths(shown.as_bytes()).unwrap(),
            key_paths,
            "{text} shown as {shown}"
        );
    }
}

#[test]
fn json_path_evaluation_is_bounded() {
    // Chained `.**` steps produce about C(depth + k - 1, k) items: 4 steps on
    // 100 nested arrays select 4.4 million, the fuzzer's 90 steps far more.
    let nested: OwnedJsonb = format!("{}{}", "[".repeat(100), "]".repeat(100))
        .parse()
        .unwrap();
    let fuzzed = "$.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.**.* .**.**.**.**.**.**.**.**.**.**.**.* .**.**.**.**.**.**.**.**.**.**.*[1].**[1]";
    for (doc, path) in [
        (nested.clone(), "$.**.**.**.**".to_string()),
        (nested.clone(), fuzzed.to_string()),
        (r#"{"a":[[[1]]]}"#.parse().unwrap(), fuzzed.to_string()),
    ] {
        let result = within_timeout(&path.clone(), move || {
            let path = parse_json_path(path.as_bytes()).unwrap();
            let raw = doc.as_raw();
            [
                raw.select_by_path(&path).map(|_| ()),
                raw.select_array_by_path(&path).map(|_| ()),
                raw.select_first_by_path(&path).map(|_| ()),
                raw.select_value_by_path(&path).map(|_| ()),
                raw.path_exists(&path).map(|_| ()),
            ]
        });
        for r in result {
            assert_eq!(r, Err(Error::JsonPathTooComplex));
        }
    }

    // Comparisons check every pair until one matches. No pair matches here,
    // so 2000 x 2000 values is 4 million comparisons.
    let list =
        |range: std::ops::Range<i32>| range.map(|i| i.to_string()).collect::<Vec<_>>().join(",");
    let values: OwnedJsonb = format!(r#"{{"a":[{}],"b":[{}]}}"#, list(0..2000), list(-2000..0))
        .parse()
        .unwrap();
    let path = parse_json_path(b"$ ? (@.a[*] < @.b[0])").unwrap();
    assert_eq!(values.as_raw().path_exists(&path), Ok(false));
    let path = parse_json_path(b"$ ? (@.a[*] < @.b[*])").unwrap();
    assert_eq!(
        values.as_raw().path_exists(&path),
        Err(Error::JsonPathTooComplex)
    );

    // Ordinary paths on large documents stay well within the budget, and
    // the budget is reset for every evaluation.
    let large: OwnedJsonb = format!(
        "[{}]",
        (0..300_000)
            .map(|i| format!("{{\"a\":{i}}}"))
            .collect::<Vec<_>>()
            .join(",")
    )
    .parse()
    .unwrap();
    let path = parse_json_path(b"$[*].a").unwrap();
    for _ in 0..3 {
        assert_eq!(large.as_raw().select_by_path(&path).unwrap().len(), 300_000);
    }
    let path = parse_json_path(b"$.**").unwrap();
    assert_eq!(large.as_raw().select_by_path(&path).unwrap().len(), 600_001);
}

#[test]
fn json_path_budget_scales_with_the_input() {
    // A fixed budget of 1,000,000 units rejected `$[*] ? (@ == 2)` above about
    // 333,000 elements (found in review).
    let count = |doc: &OwnedJsonb, path: &str| {
        let path = parse_json_path(path.as_bytes()).unwrap();
        doc.as_raw()
            .select_by_path(&path)
            .unwrap_or_else(|e| panic!("{path}: {e:?}"))
            .len()
    };
    let array = |n: usize, item: &dyn Fn(usize) -> String| -> OwnedJsonb {
        format!("[{}]", (0..n).map(item).collect::<Vec<_>>().join(","))
            .parse()
            .unwrap()
    };

    let n = 1_000_000;
    let ints = array(n, &|i| (i % 1000).to_string());
    assert_eq!(count(&ints, "$[*]"), n);
    assert_eq!(count(&ints, "$[*] ? (@ == 2)"), n / 1000);
    assert_eq!(count(&ints, "$[*] ? (@ > 0 && @ < 10)"), 9 * n / 1000);
    assert_eq!(
        count(&ints, "$[*] ? (@ == 2 || @ == 3 || @ == 4)"),
        3 * n / 1000
    );
    assert_eq!(count(&ints, "$.**"), n + 1);

    // The smallest values, 4 bytes each; every comparison is still charged.
    let nulls = array(n, &|_| "null".to_string());
    assert_eq!(count(&nulls, "$[*] ? (@ == 1 || @ == 2 || @ == 3)"), 0);

    let m = 400_000;
    let objects = array(m, &|i| format!(r#"{{"a":{},"b":"x"}}"#, i % 1000));
    assert_eq!(
        count(&objects, r#"$[*] ? (@.a == 1 && @.b == "x")"#),
        m / 1000
    );
    assert_eq!(count(&objects, "$.**"), 3 * m + 1);
}

#[test]
fn json_path_copies_are_bounded() {
    // Debug builds need more than the default stack to walk 500 levels.
    with_big_stack(|| {
        // Every ancestor of the string is selected and copied with it: 125,751
        // items, within the item budget, but about 300 MB of copies.
        let doc: OwnedJsonb = format!(
            "{}\"{}\"{}",
            "[".repeat(500),
            "x".repeat(1024),
            "]".repeat(500)
        )
        .parse()
        .unwrap();
        let path = parse_json_path(b"$.**.**").unwrap();
        let raw = doc.as_raw();
        assert_eq!(
            raw.select_by_path(&path).err(),
            Some(Error::JsonPathTooComplex)
        );
        assert_eq!(
            raw.select_array_by_path(&path).err(),
            Some(Error::JsonPathTooComplex)
        );
        assert_eq!(
            raw.select_value_by_path(&path).err(),
            Some(Error::JsonPathTooComplex)
        );
        // Checks that copy nothing are not limited by the byte budget.
        assert_eq!(raw.path_exists(&path), Ok(true));
        // A single `.**` copies 500 KiB, which is allowed.
        let path = parse_json_path(b"$.**").unwrap();
        assert_eq!(raw.select_by_path(&path).unwrap().len(), 501);
    });

    // Any single value can be copied, even one larger than 32 MiB, because
    // the budget includes the document size.
    let big: OwnedJsonb = format!(r#"{{"a":"{}","b":1}}"#, "x".repeat(33 << 20))
        .parse()
        .unwrap();
    let raw = big.as_raw();
    let path = parse_json_path(b"$.a").unwrap();
    assert_eq!(
        raw.select_first_by_path(&path).unwrap().unwrap().len(),
        // Scalar header and JEntry, then the string.
        8 + (33 << 20)
    );
    let path = parse_json_path(b"$").unwrap();
    assert_eq!(
        raw.select_first_by_path(&path).unwrap().unwrap().len(),
        raw.len()
    );
    // Copying it twice goes 33 MiB past the document size.
    let path = parse_json_path(b"$.**").unwrap();
    assert_eq!(
        raw.select_by_path(&path).err(),
        Some(Error::JsonPathTooComplex)
    );
}
