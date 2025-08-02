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
use jsonb::keypath::parse_key_paths;

#[test]
fn test_json_path() {
    let mut mint = Mint::new("tests/it/testdata");
    let mut file = mint.new_goldenfile("key_path.txt").unwrap();
    let cases = &[" {  } ", " { 1, a } ", "{1,a,-2}", r#"{a,"b","c"} "#];

    for case in cases {
        let key_paths = parse_key_paths(case.as_bytes()).unwrap();

        writeln!(file, "---------- Input ----------").unwrap();
        writeln!(file, "{case}").unwrap();
        writeln!(file, "---------- Output ---------").unwrap();
        writeln!(file, "{key_paths}").unwrap();
        writeln!(file, "---------- AST ------------").unwrap();
        writeln!(file, "{key_paths:#?}").unwrap();
        writeln!(file, "\n").unwrap();
    }
}

#[test]
fn test_json_path_error() {
    let cases = &[r#"{"#, r#"ab"#];

    for case in cases {
        let res = parse_key_paths(case.as_bytes());
        assert!(res.is_err());
    }
}
