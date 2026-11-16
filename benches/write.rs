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

//! Building and modifying JSONB, and encoding other values as JSONB.
//! See `benches/README.md` for how to run and compare.

mod common;

use criterion::criterion_group;
use criterion::criterion_main;
use criterion::Criterion;
use jsonb::jsonpath::parse_json_path;
use jsonb::parse_owned_jsonb;
use jsonb::to_owned_jsonb;
use jsonb::OwnedJsonb;

fn bench(c: &mut Criterion) {
    let object: OwnedJsonb = r#"{"a":1}"#.parse().unwrap();
    let array: OwnedJsonb = "[1,2]".parse().unwrap();
    let all = parse_json_path(b"$.**").unwrap();
    for doc in common::docs() {
        let owned = parse_owned_jsonb(&doc.text).unwrap();
        let raw = owned.as_raw();
        let value = raw.to_value().unwrap();
        let serde_value: serde_json::Value = serde_json::from_slice(&doc.text).unwrap();
        let jaq_value = jaq_json::Val::try_from(raw).unwrap();

        let mut group = common::group(c, doc.name);
        group.bench_function("build_array", |b| {
            b.iter(|| OwnedJsonb::build_array([raw]).unwrap())
        });
        group.bench_function("object_insert", |b| {
            b.iter(|| object.as_raw().object_insert("x", &raw, false).unwrap())
        });
        group.bench_function("array_insert", |b| {
            b.iter(|| array.as_raw().array_insert(0, &raw).unwrap())
        });
        group.bench_function("concat", |b| {
            b.iter(|| array.as_raw().concat(&raw).unwrap())
        });
        group.bench_function("delete_by_name", |b| {
            b.iter(|| raw.delete_by_name(doc.key).unwrap())
        });
        group.bench_function("select_array_by_path($.**)", |b| {
            b.iter(|| raw.select_array_by_path(&all).unwrap())
        });
        group.bench_function("to_owned_jsonb(serde_json)", |b| {
            b.iter(|| to_owned_jsonb(&serde_value).unwrap())
        });
        group.bench_function("Value::to_vec", |b| b.iter(|| value.to_vec().unwrap()));
        group.bench_function("OwnedJsonb::try_from(jaq)", |b| {
            b.iter(|| OwnedJsonb::try_from(&jaq_value).unwrap())
        });
        group.finish();
    }
}

criterion_group!(benches, bench);
criterion_main!(benches);
