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

use std::fs;
use std::io::Read;

use criterion::{criterion_group, criterion_main, Criterion};

fn jsonb_get(data: &[u8], paths: &[&str], expected: &str) {
    let paths = paths
        .iter()
        .map(|p| jsonb::jsonpath::Path::DotField(std::borrow::Cow::Borrowed(p)))
        .collect::<Vec<_>>();
    let json_path = jsonb::jsonpath::JsonPath { paths };

    let mut result_data = vec![];
    let mut result_offsets = vec![];

    jsonb::get_by_path(data, json_path, &mut result_data, &mut result_offsets);

    let s = jsonb::as_str(&result_data).unwrap();
    assert_eq!(s, expected);
}

fn serde_json_get(data: &[u8], paths: &Vec<&str>, expected: &str) {
    let mut v: serde_json::Value = serde_json::from_slice(data).unwrap();
    for path in paths {
        v = v.get(path).unwrap().clone();
    }
    let s = v.as_str().unwrap();
    assert_eq!(s, expected);
}

fn read(file: &str) -> Vec<u8> {
    let mut f = fs::File::open(file).unwrap();
    let mut data = vec![];
    f.read_to_end(&mut data).unwrap();
    data
}

struct TestSuite<'a> {
    file: &'a str,
    paths: Vec<&'a str>,
    expected: &'a str,
}

fn add_benchmark(c: &mut Criterion) {
    let test_suites = vec![
        TestSuite {
            file: "canada",
            paths: vec!["type"],
            expected: "FeatureCollection",
        },
        TestSuite {
            file: "citm_catalog",
            paths: vec!["areaNames", "205705994"],
            expected: "1er balcon central",
        },
        TestSuite {
            file: "citm_catalog",
            paths: vec!["topicNames", "324846100"],
            expected: "Formations musicales",
        },
        TestSuite {
            file: "twitter",
            paths: vec!["search_metadata", "max_id_str"],
            expected: "505874924095815681",
        },
    ];

    for test_suite in test_suites {
        let bytes = read(&format!("./data/{}.json", test_suite.file));

        let val = jsonb::parse_value(&bytes).unwrap();
        let jsonb_bytes = val.to_vec();

        c.bench_function(
            &format!(
                "jsonb get {}->{}",
                test_suite.file,
                test_suite.paths.join("->")
            ),
            |b| b.iter(|| jsonb_get(&jsonb_bytes, &test_suite.paths, test_suite.expected)),
        );

        c.bench_function(
            &format!(
                "serde_json get {}->{}",
                test_suite.file,
                test_suite.paths.join("->")
            ),
            |b| b.iter(|| serde_json_get(&bytes, &test_suite.paths, test_suite.expected)),
        );
    }
}

criterion_group!(benches, add_benchmark);
criterion_main!(benches);
