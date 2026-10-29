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

//! `parse_json_path` on simple paths, filters with long `&&`/`||` chains,
//! and a name that contains `&&` but no operators.
//! See `benches/README.md` for how to run and compare.

use std::hint::black_box;

use criterion::criterion_group;
use criterion::criterion_main;
use criterion::Criterion;
use jsonb::jsonpath::parse_json_path;

/// A filter with `operators` logical operators joining `@.a == 1`.
fn chain(operators: usize, op: &str) -> String {
    let conditions = vec!["@.a == 1"; operators + 1];
    format!("$ ? ({})", conditions.join(&format!(" {op} ")))
}

fn bench(c: &mut Criterion) {
    let paths = [
        ("simple", "$.store.book[0].title".to_string()),
        (
            "filter_1_op",
            r#"$.store.book[*] ? (@.price < 10 && @.category == "fiction")"#.to_string(),
        ),
        ("filter_8_ops", chain(8, "||")),
        ("filter_64_ops", chain(64, "&&")),
        ("filter_256_ops", chain(256, "||")),
        ("name_with_&&", format!("$.{}a", "a&&".repeat(50))),
    ];
    let mut group = c.benchmark_group("parse_json_path");
    for (name, path) in &paths {
        let bytes = path.as_bytes();
        assert!(parse_json_path(bytes).is_ok(), "{name}: {path}");
        group.bench_function(*name, |b| {
            b.iter(|| parse_json_path(black_box(bytes)).unwrap())
        });
    }
    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
