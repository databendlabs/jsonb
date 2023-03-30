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
use jsonb::jsonpath::tokenize;

#[test]
fn test_json_path() {
    let mut mint = Mint::new("tests/it/testdata");
    let mut file = mint.new_goldenfile("json_path.txt").unwrap();
    let cases = &[
        r#"$"#,
        r#".*"#,
        r#"..*"#,
        r#"[*]"#,
        r#".abc"#,
        r#"..def"#,
        r#"$.store.bicycle.color"#,
        r#"['key']"#,
        r#"['abc','def']"#,
        r#"[0]"#,
        r#"[1,2,3]"#,
        r#"[1:]"#,
        r#"[:7]"#,
        r#"[1:7]"#,
        r#"[1:7:2]"#,
        r#"$..book[?('a'<  'b')]"#,
        r#"$..book[?(1<=2 and 'm' = 'v')]"#,
        r#"$.price"#,
        r#"$.store.book[?($.price   > 10)]"#,
        r#"$..book[?(@.isbn)]"#,
    ];

    for case in cases {
        let tokens = tokenize(case).unwrap();
        let json_path = parse_json_path(&tokens).unwrap();
        writeln!(file, "---------- Input ----------").unwrap();
        writeln!(file, "{}", case).unwrap();
        writeln!(file, "---------- Output ---------").unwrap();
        writeln!(file, "{}", json_path).unwrap();
        writeln!(file, "---------- AST ------------").unwrap();
        writeln!(file, "{:#?}", json_path).unwrap();
        writeln!(file, "\n").unwrap();
    }
}

#[test]
fn test_json_path_error() {
    let mut mint = Mint::new("tests/it/testdata");
    let mut file = mint.new_goldenfile("json_path-error.txt").unwrap();

    let cases = &[
        r#"x"#,
        r#"$.["#,
        r#"$X"#,
        r#"$."#,
        r#"$.prop."#,
        r#"$.."#,
        r#"$.prop.."#,
        r#"$.foo bar"#,
        r#"$[0, 1, 2 4]"#,
        r#"$['1','2',]"#,
        r#"$['1', ,'3']"#,
        r#"$['aaa'}'bbb']"#,
    ];

    for case in cases {
        let tokens = tokenize(case).unwrap();
        let err = parse_json_path(&tokens).unwrap_err();
        writeln!(file, "---------- Input ----------").unwrap();
        writeln!(file, "{}", case).unwrap();
        writeln!(file, "---------- Output ---------").unwrap();
        writeln!(file, "{}", err.message()).unwrap();
    }
}
