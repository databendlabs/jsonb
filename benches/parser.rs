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

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

fn parse_jsonb(data: &[u8]) {
    let _v: jsonb::OwnedJsonb = jsonb::parse_owned_jsonb(data).unwrap();
}

fn parse_serde_json(data: &[u8]) {
    let _v: serde_json::Value = serde_json::from_slice(data).unwrap();
}

fn parse_json_deserializer(data: &[u8]) {
    let _v: json_deserializer::Value = json_deserializer::parse(data).unwrap();
}

fn parse_simd_json(data: &mut [u8]) {
    let _v = simd_json::to_borrowed_value(data).unwrap();
}

fn read(file: &str) -> Vec<u8> {
    let mut f = fs::File::open(file).unwrap();
    let mut data = vec![];
    f.read_to_end(&mut data).unwrap();
    data
}

fn add_benchmark(c: &mut Criterion) {
    let paths = fs::read_dir("./data/").unwrap();
    for path in paths {
        let file = format!("{}", path.unwrap().path().display());
        let bytes = read(&file);

        c.bench_function(&format!("jsonb parse {file}"), |b| {
            b.iter(|| parse_jsonb(&bytes))
        });

        c.bench_function(&format!("serde_json parse {file}"), |b| {
            b.iter(|| parse_serde_json(&bytes))
        });

        c.bench_function(&format!("json_deserializer parse {file}"), |b| {
            b.iter(|| parse_json_deserializer(&bytes))
        });

        let bytes = bytes.clone();
        c.bench_function(&format!("simd_json parse {file}"), move |b| {
            b.iter_batched(
                || bytes.clone(),
                |mut data| parse_simd_json(&mut data),
                BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(benches, add_benchmark);
criterion_main!(benches);
