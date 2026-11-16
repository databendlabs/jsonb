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

//! The set-like array functions, each array taken against itself.
//! See `benches/README.md` for how to run and compare.

mod common;

use criterion::criterion_group;
use criterion::criterion_main;
use criterion::Criterion;
use jsonb::jsonpath::parse_json_path;
use jsonb::parse_owned_jsonb;
use jsonb::OwnedJsonb;

fn bench(c: &mut Criterion) {
    for doc in common::docs() {
        let array: OwnedJsonb = match doc.array_path {
            Some(path) => {
                let owned = parse_owned_jsonb(&doc.text).unwrap();
                let path = parse_json_path(path.as_bytes()).unwrap();
                owned.as_raw().select_value_by_path(&path).unwrap().unwrap()
            }
            None => common::SMALL_ARRAY.parse().unwrap(),
        };
        let raw = array.as_raw();

        let mut group = common::group(c, doc.name);
        group.bench_function("array_distinct", |b| {
            b.iter(|| raw.array_distinct().unwrap())
        });
        group.bench_function("array_intersection", |b| {
            b.iter(|| raw.array_intersection(&raw).unwrap())
        });
        group.bench_function("array_except", |b| {
            b.iter(|| raw.array_except(&raw).unwrap())
        });
        group.bench_function("array_overlap", |b| {
            b.iter(|| raw.array_overlap(&raw).unwrap())
        });
        group.finish();
    }
}

criterion_group!(benches, bench);
criterion_main!(benches);
