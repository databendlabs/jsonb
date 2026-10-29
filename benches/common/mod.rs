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

//! Documents and settings shared by the `read`, `write` and `array` benches.
//! `benches/README.md` describes how to run and compare them.

#![allow(dead_code)]

use std::time::Duration;

use criterion::measurement::WallTime;
use criterion::BenchmarkGroup;
use criterion::Criterion;
use criterion::SamplingMode;

/// A small object with every scalar type, a nested object and an array.
pub const SMALL: &str = r#"{"id":12345,"name":"Alice","email":"alice@example.com","age":30,"active":true,"tags":["a","b","c"],"score":98.5,"addr":{"city":"Paris","zip":"75001"},"note":null}"#;

/// A small array of mixed types with duplicates, for the array functions.
pub const SMALL_ARRAY: &str = r#"[1,"a",true,null,{"k":1},[2,3],1,"a"]"#;

/// A JSON document with the paths and keys the benches look up in it.
pub struct Doc {
    pub name: &'static str,
    pub text: Vec<u8>,
    /// A JSONPath that selects values deep in the document.
    pub path: &'static str,
    /// A top-level key of the object.
    pub key: &'static str,
    /// A JSONPath that selects a large array, for the array functions;
    /// `None` uses [`SMALL_ARRAY`].
    pub array_path: Option<&'static str>,
}

/// The three documents in `data/` and [`SMALL`]: canada is mostly numbers,
/// citm_catalog mostly objects, and twitter mostly strings.
pub fn docs() -> Vec<Doc> {
    let read = |file: &str| {
        let path = format!("{}/data/{file}.json", env!("CARGO_MANIFEST_DIR"));
        std::fs::read(&path).unwrap_or_else(|err| panic!("{path}: {err}"))
    };
    vec![
        Doc {
            name: "canada",
            text: read("canada"),
            path: "$.features[0].geometry.coordinates[0][0]",
            key: "type",
            array_path: Some("$.features[0].geometry.coordinates[0]"),
        },
        Doc {
            name: "citm_catalog",
            text: read("citm_catalog"),
            path: "$.performances[*].seatCategories[*].areas[*].areaId",
            key: "events",
            array_path: Some("$.performances"),
        },
        Doc {
            name: "twitter",
            text: read("twitter"),
            path: "$.statuses[*].user.screen_name",
            key: "statuses",
            array_path: Some("$.statuses"),
        },
        Doc {
            name: "small",
            text: SMALL.as_bytes().to_vec(),
            path: "$.addr.city",
            key: "name",
            array_path: None,
        },
    ]
}

/// Returns a benchmark group named `name`. Operations on the large documents
/// take milliseconds, so those groups take fewer, flat samples to finish in a
/// few seconds per operation.
pub fn group<'a>(c: &'a mut Criterion, name: &str) -> BenchmarkGroup<'a, WallTime> {
    let mut group = c.benchmark_group(name);
    if name != "small" {
        group
            .sampling_mode(SamplingMode::Flat)
            .sample_size(20)
            .warm_up_time(Duration::from_secs(1))
            .measurement_time(Duration::from_secs(3));
    }
    group
}
