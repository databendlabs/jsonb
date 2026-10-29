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

//! Writes the seeds of every fuzz target into its corpus, `corpus/<target>/`,
//! one file per seed, since libFuzzer reads each file as one input. Besides typical
//! inputs, the seeds hold the tokens and boundary values of each input format,
//! so mutations can copy them. Run from the `fuzz` directory before fuzzing:
//!
//!     cargo run --bin write_seeds

use std::fs;

use jsonb::*;

/// JSON text, for `json_text`; also encoded as JSONB for `raw_jsonb`.
const JSON: &[&str] = &[
    r#"{"a":{"b":[1,2,{"c":"d"}]},"e":3.25,"f":null,"g":[true,"x"]}"#,
    r#"[[[[["x"]]]],{"y":{"z":[]}},[],{}]"#,
    r#""a\u00e9\ud83d\ude00\n\t\"\\\u0000""#,
    r#""\ud800""#,
    "[0,-0,-1.5e-7,1e400,12345678901234567890,123456789012345678901234567890.123456789,9007199254740993]",
    "[NaN,-Infinity,0x1F,-0x8000000000000000,+.5,1.,007]",
    r#"{a:1, 'b':[TRUE,NULL,1,,2,], "c":{}}"#,
    r#"{"k":"v","k":"w"}"#,
    r#"{"$serde_json::private::Number":"1"}"#,
    "-12",
    // Literals, in every spelling the extended parser accepts.
    "[null,NULL,true,TRUE,false,FALSE,NaN,nan,Infinity,-Infinity,infinity]",
    // Extended number forms and integer, decimal, and float boundaries.
    "[-0,-0.0,0.0,+1,007,.5,1.,1e-400,1e400,0x1F,0X1f.8,-0x8000000000000000]",
    "[9223372036854775807,-9223372036854775808,18446744073709551615,18446744073709551616]",
    "[99999999999999999999999999999999999999,0.00000000000000000000000000000000000001]",
    "9999999999999999999999999999999999999999999999999999999999999999999999999999",
    // Every escape, and surrogate halves.
    r#""\"\\\/\b\f\n\r\t\u0000\u001F\uD800\uDC00""#,
    // Empty elements, empty keys, single quotes, and every kind of whitespace.
    "[[,],\t{'':{\"\":[]}},\r\n [ ]]",
    // Rejected forms: incomplete exponents and braced Unicode escapes.
    "[1e,1E+]",
    r#""\u{1F600}""#,
    // Field and variant names of the serde types that `raw_jsonb` reads into.
    r#"{"id":1,"name":"n","tags":["t"],"pair":[true,1.5],"kind":{"Struct":{"x":1}},"extra":{}}"#,
    r#"[{"Newtype":1},{"Tuple":[1,"c"]},"Unit"]"#,
];

/// JSONPath, key path, and canonical key path expressions, for `json_path`.
const PATHS: &[&str] = &[
    "$.store.book[0, 1 to last - 1].price",
    "$.**{2 to last}.a",
    r#"$.store.book ? (@.price > 10.5 && (@.category == "fiction" || exists(@.isbn))).title"#,
    r#"$.a starts with "" || $[*] ? (@ == null) .name"#,
    "-$.price + 5 * 2 % 3 / 1e3 - -inf",
    r#"$."st\"ore"."book\uD83D\uDC8E".*[*]"#,
    r#"{a,"b c",-1,""}"#,
    r"user.'profile.name'[0].'it\'s'",
    // Every step and array selector.
    "$.*.**.**{2}.**{1 to last}[*][0][-1][last][last - 1][0 to last][1, 2]",
    "$[-2147483648, 2147483647]",
    // Every comparison and logical operator, and `exists`.
    r#"$ ? (exists(@.a) && @.b != 1 || @.c <> null || @.d <= true || @.e >= false)"#,
    r#"$ ? (@.f < 1.5 || @.g > "a" || @.h starts with "a")"#,
    // Escapes inside quoted names and string literals.
    r#"$["a"]."\"\\\u0041" ? (@ == "\u0041")"#,
    // Rejected forms: negation and braced Unicode escapes.
    "$ ? (!(@.c == null))",
    r#"$."\u{1F600}""#,
    "{a,0}",
];

/// Two or three JSON values separated by `0x00`, for `binary_ops`.
const VALUE_GROUPS: &[&str] = &[
    "{\"a\":1,\"b\":{\"c\":2}}\0{\"b\":{\"c\":2}}\0{\"a\":1}",
    "[1,[2,[3]],\"x\"]\0[[3]]\0\"x\"",
    "12345678901234567890\x001.2345678901234567e19\x0012345678901234567890.0",
    "9007199254740993\x009007199254740992.0\0-0.0",
    "{}\0[]\0null",
    "NaN\0-Infinity\0[TRUE,NULL,1.]",
];

/// Malformed JSONB as big-endian words: a container header (type in the top 3
/// bits, element count in the low 29), then JEntries (type in bits 28-30,
/// payload length in the low 28).
const MALFORMED_JSONB: &[&[u32]] = &[
    // Element counts far beyond the input.
    &[0x9FFF_FFFF],
    &[0x5FFF_FFFF],
    &[0x3FFF_FFFF],
    // A payload length beyond the input, and an unknown entry type.
    &[0x8000_0001, 0x0FFF_FFFF],
    &[0x8000_0002, 0x7000_0000, 0x1000_0003],
];

fn write(target: &str, seeds: impl IntoIterator<Item = Vec<u8>>) -> std::io::Result<()> {
    let dir = format!("corpus/{target}");
    fs::create_dir_all(&dir)?;
    for (i, seed) in seeds.into_iter().enumerate() {
        fs::write(format!("{dir}/seed-{i:02}"), seed)?;
    }
    Ok(())
}

fn main() -> std::io::Result<()> {
    write("json_text", JSON.iter().map(|s| s.as_bytes().to_vec()))?;
    write("json_path", PATHS.iter().map(|s| s.as_bytes().to_vec()))?;
    write(
        "binary_ops",
        VALUE_GROUPS.iter().map(|s| s.as_bytes().to_vec()),
    )?;

    let extensions = Value::Array(vec![
        Value::Binary(&[0, 1, 2]),
        Value::Date(Date { value: 19000 }),
        Value::Timestamp(Timestamp {
            value: 1_700_000_000_000_000,
        }),
        Value::TimestampTz(TimestampTz {
            offset: 3600,
            value: -1,
        }),
        Value::Interval(Interval {
            months: 14,
            days: -2,
            micros: 3_600_000_001,
        }),
    ]);
    let boundaries = Value::Array(vec![
        Value::Number(Number::Int64(i64::MIN)),
        Value::Number(Number::UInt64(u64::MAX)),
        Value::Number(Number::Float64(-0.0)),
        Value::Number(Number::Float64(f64::NAN)),
        Value::Number(Number::Decimal64(Decimal64 {
            scale: u8::MAX,
            value: 1234,
        })),
        Value::Date(Date { value: i32::MAX }),
        Value::Timestamp(Timestamp { value: i64::MIN }),
        Value::Interval(Interval {
            months: i32::MIN,
            days: i32::MIN,
            micros: i64::MIN,
        }),
    ]);
    let jsonb = JSON
        .iter()
        // Some texts are deliberately invalid, e.g. duplicate keys.
        .filter_map(|text| parse_value(text.as_bytes()).ok())
        .chain([extensions, boundaries])
        .map(|value| value.to_vec().unwrap())
        .chain(
            MALFORMED_JSONB
                .iter()
                .map(|words| words.iter().flat_map(|w| w.to_be_bytes()).collect()),
        );
    write("raw_jsonb", jsonb)?;

    // `number` reads a tag byte (0 Int64, 1 UInt64, 2 Float64, 3-5 Decimal64,
    // Decimal128, Decimal256), a scale byte for decimals, then the big-endian
    // value; each seed holds two numbers.
    let int = |v: i64| [&[0][..], &v.to_be_bytes()].concat();
    let uint = |v: u64| [&[1][..], &v.to_be_bytes()].concat();
    let float = |v: f64| [&[2][..], &v.to_be_bytes()].concat();
    let dec64 = |scale: u8, v: i64| [&[3, scale][..], &v.to_be_bytes()].concat();
    let dec128 = |scale: u8, v: i128| [&[4, scale][..], &v.to_be_bytes()].concat();
    let numbers = [
        [uint(u64::MAX), int(-1)],
        [int(i64::MIN), int(-1)],
        [dec64(2, 12_345_678_901_239_047), float(123456789012390.47)],
        [dec128(10, 10_i128.pow(30)), dec128(250, i128::MIN)],
        [float(f64::NAN), float(f64::NEG_INFINITY)],
    ];
    write("number", numbers.map(|pair| pair.concat()))
}
