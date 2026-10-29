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

//! Parsing, decoding, lookups and comparison on each document.
//! See `benches/README.md` for how to run and compare.

mod common;

use std::hint::black_box;

use criterion::criterion_group;
use criterion::criterion_main;
use criterion::Criterion;
use jsonb::from_raw_jsonb;
use jsonb::from_slice;
use jsonb::jsonpath::parse_json_path;
use jsonb::parse_owned_jsonb;

fn bench(c: &mut Criterion) {
    for doc in common::docs() {
        let owned = parse_owned_jsonb(&doc.text).unwrap();
        let raw = owned.as_raw();
        let bytes = owned.as_ref().to_vec();
        let path = parse_json_path(doc.path.as_bytes()).unwrap();
        let text = doc.text.as_slice();

        let mut group = common::group(c, doc.name);
        group.bench_function("parse_owned_jsonb", |b| {
            b.iter(|| parse_owned_jsonb(black_box(text)).unwrap())
        });
        group.bench_function("from_slice", |b| {
            b.iter(|| from_slice(black_box(&bytes)).unwrap())
        });
        group.bench_function("to_value", |b| b.iter(|| raw.to_value().unwrap()));
        group.bench_function("to_string", |b| b.iter(|| raw.to_string()));
        group.bench_function("from_raw_jsonb", |b| {
            b.iter(|| from_raw_jsonb::<serde_json::Value>(&raw).unwrap())
        });
        group.bench_function("object_each", |b| b.iter(|| raw.object_each().unwrap()));
        group.bench_function("get_by_name", |b| {
            b.iter(|| raw.get_by_name(doc.key, false).unwrap())
        });
        group.bench_function("select_by_path", |b| {
            b.iter(|| raw.select_by_path(&path).unwrap())
        });
        // Array containment is quadratic: one call on canada takes about 36 s.
        if doc.name != "canada" {
            group.bench_function("contains", |b| b.iter(|| raw.contains(&raw).unwrap()));
        }
        group.bench_function("partial_cmp", |b| b.iter(|| raw.partial_cmp(&raw)));
        group.bench_function("convert_to_comparable", |b| {
            b.iter(|| raw.convert_to_comparable())
        });
        group.bench_function("strip_nulls", |b| b.iter(|| raw.strip_nulls().unwrap()));
        group.finish();
    }
}

criterion_group!(benches, bench);
criterion_main!(benches);
