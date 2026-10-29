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

use std::io::Write;

use goldenfile::Mint;
use jsonb::jsonpath::parse_json_path;

#[test]
fn test_json_path() {
    let mut mint = Mint::new("tests/it/testdata");
    let mut file = mint.new_goldenfile("json_path.txt").unwrap();
    let cases = &[
        r#"$"#,
        r#"$.*"#,
        r#"$.**"#,
        r#"$.**{2 to last}"#,
        r#"$[*]"#,
        r#"5 + 5"#,
        r#"10 - 5"#,
        r#"10 * 5"#,
        r#"10 / 5"#,
        r#"10 % 5"#,
        r#"$.store.book[*].*"#,
        // r#"$.store.book[*].* + 5"#,
        r#"$.store.book[0].price"#,
        r#"+$.store.book[0].price"#,
        r#"-$.store.book[0].price"#,
        r#"$.store.book[0].price + 5"#,
        r#"$.store.book[last].isbn"#,
        r"$.store.book[last].test_key\uD83D\uDC8E测试",
        r#"$.store.book[0,1, last - 2].price"#,
        r#"$.store.book[0,1 to last-1]"#,
        r#"$."store"."book""#,
        r#"$."st\"ore"."book\uD83D\uDC8E""#,
        r#"$[*].book.price ? (@ == 10)"#,
        r#"$.store.book?(@.price > 10).title"#,
        r#"$.store.book?(@.price < $.expensive).price"#,
        r#"$.store.book?(@.price < 10 && @.category == "fiction")"#,
        r#"$.store.book?(@.price > 10 || @.category == "reference")"#,
        r#"$.store.book?(@.price > 20 && (@.category == "reference" || @.category == "fiction"))"#,
        // compatible with Snowflake style path
        r#"[1][2]"#,
        r#"["k1"]["k2"]"#,
        r#"k1.k2:k3"#,
        r#"k1["k2"][1]"#,
        // predicates
        r#"$ > 1"#,
        r#"$.* == 0"#,
        r#"$[*] > 1"#,
        r#"$.a > $.b"#,
        r#"$.price > 10 || $.category == "reference""#,
        // exists expression
        r#"$.store.book?(exists(@.price?(@ > 20)))"#,
        r#"$.store?(exists(@.book?(exists(@.category?(@ == "fiction")))))"#,
        r#"$.store.book?(@ starts with "Nigel")"#,
        r#"$[*] ? (@.job == null) .name"#,
        // arithmetic functions
        r#"$.phones[0].number + 3"#,
        r#"7 - $[0]"#,
        r#"- $.phones[0].number"#,
    ];

    for case in cases {
        let json_path = parse_json_path(case.as_bytes()).unwrap();

        writeln!(file, "---------- Input ----------").unwrap();
        writeln!(file, "{case}").unwrap();
        writeln!(file, "---------- Output ---------").unwrap();
        writeln!(file, "{json_path}").unwrap();
        writeln!(file, "---------- AST ------------").unwrap();
        writeln!(file, "{json_path:#?}").unwrap();
        writeln!(file, "\n").unwrap();
    }
}

#[test]
fn test_json_path_error() {
    let cases = &[
        r#"$.["#,
        r#"$X"#,
        r#"$."#,
        r#"$.prop."#,
        r#"$.prop+."#,
        r#"$.."#,
        r#"$.prop.."#,
        r#"$.foo bar"#,
        r#"$[0, 1, 2 4]"#,
        r#"$['1','2',]"#,
        r#"$['1', ,'3']"#,
        r#"$['aaa'}'bbb']"#,
        r#"@ > 10"#,
        // Unterminated quoted fields, including escaped and UTF-8 content.
        r#"$."a"#,
        r#""a"#,
        r#"$["a"#,
        r#"$."a\""#,
        r#"$."a\\"#,
        r#"$."\u0061"#,
        r#"$."中文"#,
        r#"$.a ? (@ == "value"#,
    ];

    for case in cases {
        let res = parse_json_path(case.as_bytes());
        assert!(res.is_err());
    }
}

#[test]
fn test_json_path_number_literals() {
    // Each case is (input, formatted). Literals with a fraction or exponent
    // used to fail to parse: the integer parser took `1` from `1.5` and left
    // `.5`, which no rule accepts (found by fuzzing).
    let cases = [
        ("$ ? (@ > 1.5)", "$?(@ > 1.5)"),
        ("$ ? (@ == -1.5e3)", "$?(@ == -1500.0)"),
        ("$ ? (@ == 1E+3)", "$?(@ == 1000.0)"),
        ("$ ? (@ == 1.)", "$?(@ == 1.0)"),
        ("$ ? (@ == .5)", "$?(@ == 0.5)"),
        ("$ ? (@ == -0.0)", "$?(@ == -0.0)"),
        (
            "$ ? (@ == 18446744073709551615)",
            "$?(@ == 18446744073709551615)",
        ),
        (
            "$ ? (@ == -9223372036854775808)",
            "$?(@ == -9223372036854775808)",
        ),
        (
            "$ ? (@ == 18446744073709551616)",
            "$?(@ == 1.8446744073709552e+19)",
        ),
        (".0/5", "0.0 / 5"),
        ("1e16 / 5", "1e+16 / 5"),
        ("inf / 5", "inf / 5"),
        // Overflowing literals become infinities, which `Display` writes with
        // a sign, so signed `inf`, `infinity` and `nan` must parse too.
        ("0 > -1e400", "0 > -inf"),
        ("0 > -inf", "0 > -inf"),
        ("$ ? (@ == -Infinity)", "$?(@ == -inf)"),
        ("0 > +nan", "0 > NaN"),
        // Not number literals: these stay field names.
        ("0.0", ".0.0"),
        ("1e.a", ".1e.a"),
    ];
    for (input, formatted) in cases {
        let path = parse_json_path(input.as_bytes()).unwrap();
        let text = path.to_string();
        assert_eq!(text, formatted, "{input}");
        assert_eq!(parse_json_path(text.as_bytes()).unwrap(), path, "{input}");
    }
}

#[test]
fn test_json_path_logical_parentheses() {
    // Each case is (input, formatted). Parentheses are kept only where the
    // tree differs from the parser's precedence (`&&` over `||`) and
    // left-to-right grouping.
    let cases = [
        (
            "$ ? (@.a == 1 || @.b == 2 || @.c == 3)",
            "$?(@.a == 1 || @.b == 2 || @.c == 3)",
        ),
        (
            "$ ? ((@.a == 1 && @.b == 2) && @.c == 3)",
            "$?(@.a == 1 && @.b == 2 && @.c == 3)",
        ),
        (
            "$ ? (@.a == 1 || @.b == 2 && @.c == 3)",
            "$?(@.a == 1 || @.b == 2 && @.c == 3)",
        ),
        (
            "$ ? ((@.a == 1 || @.b == 2) && @.c == 3)",
            "$?((@.a == 1 || @.b == 2) && @.c == 3)",
        ),
        (
            "$ ? (@.a == 1 && (@.b == 2 || @.c == 3))",
            "$?(@.a == 1 && (@.b == 2 || @.c == 3))",
        ),
        (
            "$ ? (@.a == 1 || (@.b == 2 || @.c == 3))",
            "$?(@.a == 1 || (@.b == 2 || @.c == 3))",
        ),
        (
            "$ ? (@.a == 1 && (@.b == 2 && @.c == 3))",
            "$?(@.a == 1 && (@.b == 2 && @.c == 3))",
        ),
    ];
    for (input, formatted) in cases {
        let path = parse_json_path(input.as_bytes()).unwrap();
        let text = path.to_string();
        assert_eq!(text, formatted, "{input}");
        assert_eq!(parse_json_path(text.as_bytes()).unwrap(), path, "{input}");
    }

    // A chain of 120 `||` used to format with 119 nested parentheses, past
    // the parser's limit of 64 (found by fuzzing).
    let chain = vec!["$.a - 5"; 120].join(" || ");
    let path = parse_json_path(chain.as_bytes()).unwrap();
    let text = path.to_string();
    assert_eq!(text, chain);
    assert_eq!(parse_json_path(text.as_bytes()).unwrap(), path);
}

#[test]
fn test_json_path_empty_string() {
    use jsonb::OwnedJsonb;

    // `""` is a valid string literal and a valid quoted name. The quoted-string
    // parser used to reject it, so comparing with an empty string failed.
    let doc: OwnedJsonb = r#"{"":{"x":1},"a":"","b":"c"}"#.parse().unwrap();
    let cases = [
        (r#"$ ? (@.a == "")"#, r#"$?(@.a == "")"#, true),
        (r#"$ ? (@.b == "")"#, r#"$?(@.b == "")"#, false),
        (r#"$."".x"#, r#"$."".x"#, true),
        (r#"$[""]"#, r#"$[""]"#, true),
        (r#"$.b starts with """#, r#"$.b starts with """#, true),
    ];
    for (input, formatted, exists) in cases {
        let path = parse_json_path(input.as_bytes()).unwrap();
        let text = path.to_string();
        assert_eq!(text, formatted, "{input}");
        assert_eq!(parse_json_path(text.as_bytes()).unwrap(), path, "{input}");
        let result = if path.is_predicate() {
            doc.as_raw().path_match(&path).unwrap() == Some(true)
        } else {
            doc.as_raw().path_exists(&path).unwrap()
        };
        assert_eq!(result, exists, "{input}");
    }
}
