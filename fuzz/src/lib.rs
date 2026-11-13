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

//! Shared checks for the jsonb fuzz targets.
//!
//! Every public API must handle arbitrary input without panicking, overflowing
//! the stack, or allocating memory out of proportion to the input. On top of
//! that, each check asserts invariants that hold by design, so a failing
//! assertion is a bug rather than a quirk of malformed input.

mod model;

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use jsonb::jsonpath::parse_json_path;
use jsonb::keypath::parse_key_paths;
use jsonb::keypath::KeyPath;
use jsonb::keypath::OwnedKeyPaths;
use jsonb::*;
use serde::Deserialize;

/// Valid documents that path and binary-operation checks run against.
const DOCUMENTS: &[&str] = &[
    r#"{"a":{"b":[1,2,{"c":"d"}]},"e":3.25,"f":null,"g":[true,"x",[1,[2]]]}"#,
    r#"[1,"a",null,{"k":[true,2.5]},[[]],{"a":{"a":1}}]"#,
    r#""text""#,
    "-12",
];

fn documents() -> Vec<OwnedJsonb> {
    DOCUMENTS.iter().map(|text| text.parse().unwrap()).collect()
}

/// Types that drive most of serde's `Deserializer` entry points.
#[derive(Deserialize)]
#[allow(dead_code)]
struct Record {
    id: Option<u64>,
    name: String,
    tags: Vec<String>,
    pair: (bool, f64),
    kind: Kind,
    extra: BTreeMap<String, serde_json::Value>,
}

#[derive(Deserialize)]
#[allow(dead_code)]
enum Kind {
    Unit,
    Newtype(i32),
    Tuple(u8, char),
    Struct { x: i16 },
}

/// Calls every public read and transform API on one value, discarding the
/// results: arbitrary bytes may be rejected with any error, but never panic.
pub fn exercise_unary(raw: RawJsonb<'_>) {
    let keys = BTreeSet::from(["a", "k", ""]);
    let _ = (
        from_slice(raw.as_ref()),
        raw.to_value().map(|v| v.to_string()),
    );
    let _ = (raw.to_string(), raw.to_pretty_string());
    let _ = (serde_json::to_string(&raw), serde_json::to_value(raw));
    let _ = from_raw_jsonb::<serde_json::Value>(&raw);
    let _ = (from_raw_jsonb::<String>(&raw), from_raw_jsonb::<char>(&raw));
    let _ = (from_raw_jsonb::<i8>(&raw), from_raw_jsonb::<u64>(&raw));
    let _ = from_raw_jsonb::<f32>(&raw);
    let _ = from_raw_jsonb::<Vec<Option<bool>>>(&raw);
    let _ = from_raw_jsonb::<BTreeMap<String, String>>(&raw);
    let _ = (from_raw_jsonb::<Record>(&raw), from_raw_jsonb::<Kind>(&raw));
    let _ = jaq_json::Val::try_from(raw).map(|val| val.to_string());

    let _ = (raw.jsonb_item_type(), raw.type_of(), raw.is_null());
    let _ = (raw.is_string(), raw.as_null(), raw.as_bool(), raw.to_bool());
    let _ = (raw.as_str(), raw.to_str(), raw.as_i64(), raw.as_u64());
    let _ = (raw.as_f64(), raw.to_i64(), raw.to_u64(), raw.to_f64());
    let _ = raw.as_number().map(|n| n.map(|n| n.to_string()));
    let _ = raw.as_extension_value().map(|v| v.map(|v| v.to_string()));
    let _ = (
        raw.as_binary(),
        raw.as_date().map(|v| v.map(|v| v.to_string())),
    );
    let _ = raw.as_timestamp().map(|v| v.map(|v| v.to_string()));
    let _ = raw.as_timestamp_tz().map(|v| v.map(|v| v.to_string()));
    let _ = raw.as_interval().map(|v| v.map(|v| v.to_string()));

    let _ = (raw.array_length(), raw.array_values(), raw.array_distinct());
    let _ = (raw.array_insert(0, &raw), raw.array_insert(-1, &raw));
    let _ = (raw.object_keys(), raw.object_each());
    let _ = (raw.object_delete(&keys), raw.object_pick(&keys));
    let _ = raw.object_insert("a", &raw, true);
    let _ = raw.object_insert("new", &raw, false);
    let _ = (raw.get_by_index(0), raw.get_by_index(usize::MAX));
    let _ = (raw.get_by_name("a", false), raw.get_by_name("A", true));
    let _ = (raw.delete_by_index(-1), raw.delete_by_index(i32::MIN));
    let _ = raw.delete_by_name("a");
    let _ = raw.exists_any_keys(["a", "k"].into_iter());
    let _ = raw.exists_all_keys(["a", "k"].into_iter());
    let _ = (raw.strip_nulls(), raw.convert_to_comparable());
    let _ = raw.traverse_check_string(|s| s.is_empty());
    let _ = raw.visit_scalar_key_paths(false, |_| Ok(()));
    let _ = raw.visit_scalar_key_values(true, |_, value| {
        let _ = value.to_string();
        Ok(())
    });
    exercise_binary(raw, raw);
}

/// Calls every two-value API on `left` and `right`, in both directions.
pub fn exercise_binary(left: RawJsonb<'_>, right: RawJsonb<'_>) {
    for (a, b) in [(left, right), (right, left)] {
        let _ = (a.partial_cmp(&b), a.cmp(&b), a.contains(&b));
        let _ = a.concat(&b).map(|o| o.to_string());
        let _ = (a.array_intersection(&b), a.array_except(&b));
        let _ = (a.array_overlap(&b), a.array_insert(1, &b));
        let _ = (
            a.object_insert("k", &b, true),
            a.object_insert("z", &b, false),
        );
        let _ = OwnedJsonb::build_array([a, b]).map(|o| o.to_string());
        let _ = OwnedJsonb::build_object([("a", a), ("b", b)]).map(|o| o.to_string());
    }
}

/// Fuzzes arbitrary bytes interpreted as JSONB.
///
/// A value that decodes must survive a round trip: re-encoding it and
/// decoding again yields an equal value, and that second encoding is stable.
pub fn check_raw_jsonb(data: &[u8]) {
    let raw = RawJsonb::new(data);
    exercise_unary(raw);
    for document in documents() {
        exercise_binary(raw, document.as_raw());
    }
    if let Ok(value) = raw.to_value() {
        let encoded = value.to_vec().expect("a decoded value re-encodes");
        let decoded = RawJsonb::new(&encoded)
            .to_value()
            .expect("re-encoded bytes decode");
        assert_eq!(value, decoded, "round trip changed the value");
        assert_eq!(encoded, decoded.to_vec().unwrap(), "encoding is not stable");
        check_canonical(RawJsonb::new(&encoded));
    }
}

/// Checks invariants of JSONB produced by this crate's own encoder.
fn check_canonical(raw: RawJsonb<'_>) {
    let value = raw.to_value().expect("canonical JSONB decodes");
    assert_eq!(
        from_slice(raw.as_ref()).unwrap(),
        value,
        "from_slice and to_value disagree"
    );
    assert_eq!(
        raw.partial_cmp(&raw),
        Some(Ordering::Equal),
        "a value must equal itself"
    );
    check_functions(raw, &value);
}

/// Panics unless a function result matches its model. `None` stands for an
/// error, or for a missing value where the function returns an `Option`.
fn assert_model(got: Option<OwnedJsonb>, expect: Option<Value<'_>>, what: impl Fn() -> String) {
    let got = got.as_ref().map(decode);
    if got != expect {
        let show = |v: Option<&Value<'_>>| v.map_or("an error".to_string(), |v| v.to_string());
        panic!(
            "{}: got {}, expected {}",
            what(),
            show(got.as_ref()),
            show(expect.as_ref())
        );
    }
}

/// Names worth probing in `value`: its own keys or string elements, their
/// ASCII case variants, and names that are usually absent.
fn probe_names(value: &Value<'_>) -> Vec<String> {
    let mut names: BTreeSet<String> = match value {
        Value::Object(object) => object.keys().take(4).cloned().collect(),
        Value::Array(items) => {
            let strings = items.iter().filter_map(|item| item.as_str());
            strings.take(4).map(|s| s.to_string()).collect()
        }
        Value::String(s) => BTreeSet::from([s.to_string()]),
        _ => BTreeSet::new(),
    };
    let variants: Vec<String> = names
        .iter()
        .flat_map(|name| [name.to_ascii_uppercase(), name.to_ascii_lowercase()])
        .collect();
    names.extend(variants);
    names.extend(["", "a", "missing"].map(String::from));
    names.into_iter().collect()
}

/// Checks `RawJsonb` functions on valid JSONB against the models in
/// [`model`], with arguments taken from the value itself.
fn check_functions(raw: RawJsonb<'_>, value: &Value<'_>) {
    // Compares a result with its model; the message names the call.
    macro_rules! same {
        ($got:expr, $expect:expr) => {
            assert_model($got, $expect, || format!("{} on {value}", stringify!($got)))
        };
    }

    let names = probe_names(value);
    for name in &names {
        for flag in [false, true] {
            same!(
                raw.get_by_name(name, flag).unwrap(),
                model::get_by_name(value, name, flag)
            );
            let expect = model::object_insert(value, name, value, flag);
            same!(raw.object_insert(name, &raw, flag).ok(), expect);
        }
        same!(
            raw.delete_by_name(name).ok(),
            model::delete_by_name(value, name)
        );
    }

    let (first, second) = (names[0].as_str(), names[1].as_str());
    for keys in [vec![], vec![first], vec![first, second, "missing"]] {
        let any = raw.exists_any_keys(keys.iter().copied()).unwrap();
        let all = raw.exists_all_keys(keys.iter().copied()).unwrap();
        let expect = (
            model::exists_any_keys(value, &keys),
            model::exists_all_keys(value, &keys),
        );
        assert_eq!(
            (any, all),
            expect,
            "exists_any/all_keys({keys:?}) on {value}"
        );
        let set: BTreeSet<&str> = keys.iter().copied().collect();
        same!(
            raw.object_delete(&set).ok(),
            model::object_delete(value, &set)
        );
        same!(raw.object_pick(&set).ok(), model::object_pick(value, &set));
    }

    let items = value.as_array();
    assert_eq!(
        raw.array_length().unwrap(),
        items.map(Vec::len),
        "array_length of {value}"
    );
    let len = items.map_or(0, Vec::len);
    for index in BTreeSet::from([0, 1, len.wrapping_sub(1), len, len + 1, usize::MAX]) {
        same!(
            raw.get_by_index(index).unwrap(),
            items.and_then(|items| items.get(index)).cloned()
        );
    }
    let len = i32::try_from(len).unwrap_or(i32::MAX);
    for index in BTreeSet::from([
        0,
        1,
        -1,
        -2,
        len - 1,
        len,
        -len,
        -len - 1,
        i32::MIN,
        i32::MAX,
    ]) {
        same!(
            raw.delete_by_index(index).ok(),
            model::delete_by_index(value, index)
        );
    }

    let values = raw.array_values().unwrap();
    let values: Option<Vec<Value<'_>>> = values.as_ref().map(|v| v.iter().map(decode).collect());
    assert_eq!(values.as_ref(), items, "array_values of {value}");
    let each = raw.object_each().unwrap();
    let each: Option<Vec<(&str, Value<'_>)>> = each
        .as_ref()
        .map(|each| each.iter().map(|(k, v)| (k.as_str(), decode(v))).collect());
    let object = value.as_object();
    let expect = object.map(|o| o.iter().map(|(k, v)| (k.as_str(), v.clone())).collect());
    assert_eq!(each, expect, "object_each of {value}");
    same!(raw.object_keys().unwrap(), model::object_keys(value));
    same!(raw.strip_nulls().ok(), Some(model::strip_nulls(value)));
    let contains = raw.contains(&raw).unwrap();
    assert_eq!(
        contains,
        model::contains(value, value),
        "contains(self, self) of {value}"
    );

    // Extraction collects exactly what the visitor sees.
    for ignore_array in [false, true] {
        let extracted = raw.extract_scalar_key_values(ignore_array).unwrap();
        let extracted: Vec<(Vec<KeyPath<'_>>, Value<'_>)> = extracted
            .into_iter()
            .map(|(paths, value)| (paths.paths, value))
            .collect();
        let mut visited = Vec::new();
        raw.visit_scalar_key_values(ignore_array, |paths, value| {
            visited.push((paths.to_vec(), value));
            Ok(())
        })
        .unwrap();
        assert_eq!(extracted, visited, "extract_scalar_key_values of {value}");
    }
}

/// Decodes JSONB produced by a function under test.
fn decode(owned: &OwnedJsonb) -> Value<'_> {
    owned.as_raw().to_value().expect("function results decode")
}

/// Writes into a buffer that already holds bytes, and returns what was
/// appended. Writers must append, and a failed write must append nothing.
fn appended(write: impl FnOnce(&mut Vec<u8>) -> Result<(), Error>) -> Result<Vec<u8>, Error> {
    const PREFIX: &[u8] = b"prefix";
    let mut buf = PREFIX.to_vec();
    let result = write(&mut buf);
    assert_eq!(
        &buf[..PREFIX.len()],
        PREFIX,
        "a writer changed existing bytes"
    );
    let written = buf.split_off(PREFIX.len());
    assert!(
        result.is_ok() || written.is_empty(),
        "a failed write left output behind"
    );
    result.map(|()| written)
}

/// The JSON text parsers of one syntax mode: to JSONB, to JSONB in a given
/// buffer, and to a `Value`.
type ParseMode = (
    fn(&[u8]) -> Result<OwnedJsonb, Error>,
    fn(&[u8], &mut Vec<u8>) -> Result<(), Error>,
    fn(&[u8]) -> Result<Value<'_>, Error>,
);

/// Fuzzes arbitrary bytes interpreted as JSON text.
///
/// All encoders must agree byte for byte, `Value` and `RawJsonb` must format
/// the same JSON, and that text must parse back to an equal value. Standard
/// mode must also accept what `serde_json` accepts.
pub fn check_json_text(data: &[u8]) {
    check_against_serde_json(data);
    let modes: [ParseMode; 2] = [
        (parse_owned_jsonb, parse_owned_jsonb_with_buf, parse_value),
        (
            parse_owned_jsonb_standard_mode,
            parse_owned_jsonb_standard_mode_with_buf,
            parse_value_standard_mode,
        ),
    ];
    for (parse_owned, parse_owned_with_buf, parse) in modes {
        let owned = parse_owned(data);
        let with_buf = appended(|buf| parse_owned_with_buf(data, buf));
        let value = parse(data);
        let (owned, value) = match (owned, value) {
            (Ok(owned), Ok(value)) => (owned, value),
            (Err(_), Err(_)) => {
                assert!(
                    with_buf.is_err(),
                    "only the _with_buf parser accepts the input"
                );
                continue;
            }
            (owned, value) => panic!("parsers disagree: {owned:?} vs {value:?}"),
        };
        let encoded = value.to_vec().expect("a parsed value encodes");
        assert_eq!(
            owned.as_ref(),
            encoded,
            "parse_owned_jsonb and to_vec disagree"
        );
        let with_buf = with_buf.expect("only the _with_buf parser rejects the input");
        assert_eq!(with_buf, encoded, "the _with_buf parser disagrees");
        assert_eq!(
            appended(|buf| value.write_to_vec(buf)).unwrap(),
            encoded,
            "write_to_vec disagrees"
        );

        let raw = owned.as_raw();
        check_canonical(raw);
        exercise_unary(raw);

        // `Value` writes the same JSON as `RawJsonb`. `IgnoredAny` checks the
        // syntax only: a `serde_json::Value` would misread objects keyed by
        // serde_json's private number marker.
        let text = raw.to_string();
        assert_eq!(
            value.to_string(),
            text,
            "Value and RawJsonb format differently"
        );
        if let Err(err) = serde_json::from_str::<serde::de::IgnoredAny>(&text) {
            panic!("formatted text {text:?} is not JSON: {err}");
        }

        // Reparsing keeps the value. The text may change once, e.g. `-0.0` as
        // a float reparses as the decimal `0.0`, but is stable after that. JSON
        // has no NaN or infinity, which format as `null`, so only stability
        // holds for them.
        let reparse = |text: &str| {
            parse_owned_jsonb(text.as_bytes())
                .unwrap_or_else(|err| panic!("formatted text {text:?} does not parse: {err}"))
        };
        let reparsed = reparse(&text);
        if !has_non_finite_float(&value) {
            let order = reparsed.as_raw().partial_cmp(&raw);
            assert_eq!(
                order,
                Some(Ordering::Equal),
                "reparsing {text:?} changed the value"
            );
        }
        let stable = reparsed.to_string();
        assert_eq!(
            reparse(&stable).to_string(),
            stable,
            "formatting is not stable"
        );
    }
}

/// Checks that standard mode accepts what `serde_json` accepts, with the same
/// meaning.
///
/// Only this direction holds: standard mode knowingly accepts raw control
/// characters and lone surrogates that `serde_json` rejects. It rejects
/// duplicate object keys by design, which `serde_json` accepts.
fn check_against_serde_json(data: &[u8]) {
    // With `arbitrary_precision`, serde_json reads an object keyed by this
    // marker as a number, so its `Value` is not a faithful reference.
    const SERDE_NUMBER_KEY: &[u8] = b"$serde_json::private::Number";
    if data
        .windows(SERDE_NUMBER_KEY.len())
        .any(|w| w == SERDE_NUMBER_KEY)
    {
        return;
    }
    let Ok(expect) = serde_json::from_slice::<serde_json::Value>(data) else {
        return;
    };
    match parse_value_standard_mode(data) {
        Ok(got) => assert!(
            same_as_serde_json(&got, &expect),
            "standard mode parses {got}, serde_json parses {expect}"
        ),
        Err(err) if err.to_string().starts_with("duplicate object attribute") => {}
        Err(err) => panic!("standard mode rejects JSON that serde_json accepts: {err}"),
    }
}

/// Compares a parsed `Value` with a `serde_json::Value` of the same text.
fn same_as_serde_json(got: &Value<'_>, expect: &serde_json::Value) -> bool {
    use serde_json::Value as Json;
    match (got, expect) {
        (Value::Null, Json::Null) => true,
        (Value::Bool(a), Json::Bool(b)) => a == b,
        (Value::String(a), Json::String(b)) => a == b,
        // Representations differ by design (decimals, overflow to infinity),
        // so compare with this crate's reading of the digits serde_json kept.
        (Value::Number(a), Json::Number(b)) => {
            matches!(parse_value_standard_mode(b.to_string().as_bytes()), Ok(Value::Number(b)) if *a == b)
        }
        (Value::Array(a), Json::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| same_as_serde_json(a, b))
        }
        (Value::Object(a), Json::Object(b)) => {
            a.len() == b.len()
                && b.iter()
                    .all(|(k, b)| a.get(k).is_some_and(|a| same_as_serde_json(a, b)))
        }
        _ => false,
    }
}

/// Returns whether `value` contains NaN or an infinity.
fn has_non_finite_float(value: &Value<'_>) -> bool {
    match value {
        Value::Number(Number::Float64(v)) => !v.is_finite(),
        Value::Array(items) => items.iter().any(has_non_finite_float),
        Value::Object(object) => object.values().any(has_non_finite_float),
        _ => false,
    }
}

/// Fuzzes arbitrary bytes interpreted as a JSONPath, key path, or canonical
/// key path.
///
/// Evaluating a path must not panic, and every path that parses must format to
/// text that parses back to the same path.
pub fn check_path(data: &[u8]) {
    let documents = documents();
    let json_path = parse_json_path(data);
    let key_paths = parse_key_paths(data);
    for document in &documents {
        let raw = document.as_raw();
        if let Ok(path) = &json_path {
            let _ = (raw.select_by_path(path), raw.select_array_by_path(path));
            let _ = (
                raw.select_first_by_path(path),
                raw.select_value_by_path(path),
            );
            let _ = (raw.path_exists(path), raw.path_match(path));
        }
        if let Ok(key_paths) = &key_paths {
            let _ = raw.get_by_keypath(key_paths.paths.iter());
            let _ = raw.delete_by_keypath(key_paths.paths.iter());
        }
    }

    // Formatting checks run after evaluation, so that a formatting bug does
    // not keep the fuzzer from exploring evaluation.
    if let Ok(path) = json_path {
        let text = path.to_string();
        let reparsed = parse_json_path(text.as_bytes())
            .unwrap_or_else(|err| panic!("formatted path {text:?} does not parse: {err}"));
        assert_eq!(path, reparsed, "path changed after formatting as {text:?}");
    }
    if let Ok(key_paths) = key_paths {
        let text = key_paths.to_string();
        let reparsed = parse_key_paths(text.as_bytes())
            .unwrap_or_else(|err| panic!("formatted key path {text:?} does not parse: {err}"));
        assert_eq!(
            key_paths, reparsed,
            "key path changed after formatting as {text:?}"
        );

        // The canonical form used by virtual-column metadata round-trips. It
        // has no form for the empty path, which names no virtual column.
        let owned = key_paths.to_owned();
        if !owned.paths.is_empty() {
            let canonical = owned.to_canonical_path();
            let decoded = OwnedKeyPaths::from_canonical_path(&canonical).unwrap_or_else(|err| {
                panic!("canonical path {canonical:?} does not decode: {err}")
            });
            assert_eq!(
                decoded, owned,
                "canonical path {canonical:?} changed the key path"
            );
        }
    }
    if let Ok(Ok(decoded)) = std::str::from_utf8(data).map(OwnedKeyPaths::from_canonical_path) {
        let canonical = decoded.to_canonical_path();
        let again = OwnedKeyPaths::from_canonical_path(&canonical).ok();
        assert_eq!(
            again,
            Some(decoded),
            "re-encoding canonical path as {canonical:?} changed it"
        );
    }
}

/// Reads a `Number` of any variant from the front of `data`: a tag byte, a
/// scale byte for decimals, then the big-endian value.
fn read_number(data: &mut &[u8]) -> Option<Number> {
    fn take<const N: usize>(data: &mut &[u8]) -> Option<[u8; N]> {
        let (head, rest) = data.split_first_chunk::<N>()?;
        *data = rest;
        Some(*head)
    }
    let [tag] = take(data)?;
    Some(match tag % 6 {
        0 => Number::Int64(i64::from_be_bytes(take(data)?)),
        1 => Number::UInt64(u64::from_be_bytes(take(data)?)),
        2 => Number::Float64(f64::from_be_bytes(take(data)?)),
        tag => {
            let [scale] = take(data)?;
            match tag {
                3 => Number::Decimal64(Decimal64 {
                    scale,
                    value: i64::from_be_bytes(take(data)?),
                }),
                4 => Number::Decimal128(Decimal128 {
                    scale,
                    value: i128::from_be_bytes(take(data)?),
                }),
                _ => Number::Decimal256(Decimal256 {
                    scale,
                    value: ethnum::i256::from_be_bytes(take(data)?),
                }),
            }
        }
    })
}

/// The exact value of an integer `Number`, and whether its type is signed.
fn integer_value(number: &Number) -> Option<(i128, bool)> {
    match number {
        Number::Int64(v) => Some((i128::from(*v), true)),
        Number::UInt64(v) => Some((i128::from(*v), false)),
        _ => None,
    }
}

/// A `Number` arithmetic method, paired with the same operation on exact
/// integers.
type ArithmeticOp = (
    &'static str,
    fn(&Number, Number) -> Result<Number, Error>,
    fn(i128, i128) -> Option<i128>,
);

/// Fuzzes two `Number`s built from arbitrary bytes.
///
/// Arithmetic, conversion, and formatting must not panic. Integer arithmetic
/// must never return a wrong value, and may fail only when the exact result
/// does not fit the result type. Comparison must be antisymmetric and the
/// comparable encoding must never reverse it. Formatted numbers must parse
/// back to equal values.
pub fn check_number(mut data: &[u8]) {
    let (Some(a), Some(b)) = (read_number(&mut data), read_number(&mut data)) else {
        return;
    };
    check_number_unary(&a);
    check_number_unary(&b);

    let ops: [ArithmeticOp; 4] = [
        ("add", Number::add, i128::checked_add),
        ("sub", Number::sub, i128::checked_sub),
        ("mul", Number::mul, i128::checked_mul),
        ("rem", Number::rem, i128::checked_rem),
    ];
    for (x, y) in [(&a, &b), (&b, &a)] {
        let _ = x.div(y.clone()).map(|n| n.to_string());
        for (name, op, exact) in ops {
            let result = op(x, y.clone());
            let _ = result.as_ref().map(Number::to_string);
            let (Some((xi, x_signed)), Some((yi, y_signed))) = (integer_value(x), integer_value(y))
            else {
                continue;
            };
            let expect = exact(xi, yi);
            match result {
                // A result is never silently wrong.
                Ok(got) => assert_eq!(
                    integer_value(&got).map(|(v, _)| v),
                    expect,
                    "{x:?} {name} {y:?} returned {got:?}"
                ),
                // An error means the exact result does not fit the result
                // type: `i64` for two `Int64`, `u64` for two `UInt64`, and
                // neither for mixed operands.
                Err(err) => {
                    let fits_i64 = |v: i128| i64::try_from(v).is_ok();
                    let fits_u64 = |v: i128| u64::try_from(v).is_ok();
                    let representable = expect.is_some_and(|v| match (x_signed, y_signed) {
                        (true, true) => fits_i64(v),
                        (false, false) => fits_u64(v),
                        _ => fits_i64(v) || fits_u64(v),
                    });
                    assert!(
                        !representable,
                        "{x:?} {name} {y:?} failed with {err:?}, expected {expect:?}"
                    );
                }
            }
        }
    }

    let order = a.cmp(&b);
    assert_eq!(
        order,
        b.cmp(&a).reverse(),
        "comparison is not antisymmetric: {a:?} vs {b:?}"
    );
    let comparable = |n: &Number| {
        let encoded = Value::Number(n.clone()).to_vec().unwrap();
        RawJsonb::new(&encoded).convert_to_comparable()
    };
    let encoded = comparable(&a).cmp(&comparable(&b));
    assert_comparable_order(order, encoded, || format!("{a:?} vs {b:?}"));
}

/// Panics if the comparable encoding orders two values the opposite way from
/// `order`, their exact comparison.
///
/// The encoding may map different values to the same bytes: it converts
/// numbers to `f64`, so integers beyond 2^53 and decimals that differ only past
/// the 17th significant digit encode equally. That loss is known; reversing an
/// order is not.
fn assert_comparable_order(order: Ordering, encoded: Ordering, what: impl Fn() -> String) {
    assert!(
        encoded == order || encoded == Ordering::Equal,
        "comparable encoding reverses the order of {}: {order:?} but encoded {encoded:?}",
        what()
    );
}

/// Checks the single-number APIs on `n`.
fn check_number_unary(n: &Number) {
    let _ = (
        n.as_i64(),
        n.as_u64(),
        n.to_i64(),
        n.to_u64(),
        n.to_i128(),
        n.as_f64(),
    );
    if let Some(v) = n.as_i128() {
        let exact = Number::Decimal128(Decimal128 { scale: 0, value: v });
        assert_eq!(
            n.cmp(&exact),
            Ordering::Equal,
            "as_i128 of {n:?} returned {v}"
        );
    }
    // Negating back may overflow (`UInt64(2^63)` negates to `i64::MIN`), but
    // must not return a different value.
    if let Ok(back) = n.neg().and_then(|negated| negated.neg()) {
        assert_eq!(
            back.cmp(n),
            Ordering::Equal,
            "negating {n:?} twice returned {back:?}"
        );
    }
    if n.as_f64().is_finite() {
        let text = n.to_string();
        match parse_value(text.as_bytes()) {
            Ok(Value::Number(reparsed)) if reparsed.cmp(n) == Ordering::Equal => {}
            other => panic!("{n:?} formats as {text:?}, which parses as {other:?}"),
        }
    }
}

/// Fuzzes two or three values separated by `0x00` bytes.
///
/// Each part is parsed as JSON text when possible, so most inputs reach the
/// binary operations with valid JSONB; otherwise the raw bytes are used. For
/// valid values, `concat` and `contains` must match their models,
/// `RawJsonb::partial_cmp` and `Value::cmp` must agree and form a total
/// order, and the byte order of `convert_to_comparable` must never reverse it.
pub fn check_binary_ops(data: &[u8]) {
    let parts: Vec<&[u8]> = data.splitn(3, |&b| b == 0).collect();
    let owned: Vec<Option<OwnedJsonb>> = parts
        .iter()
        .map(|part| parse_owned_jsonb(part).ok())
        .collect();
    let raw = |i: usize| match (owned.get(i), parts.get(i)) {
        (Some(Some(owned)), _) => owned.as_raw(),
        (_, Some(part)) => RawJsonb::new(part),
        _ => RawJsonb::new(&[]),
    };
    exercise_binary(raw(0), raw(1));

    let valid: Vec<(RawJsonb<'_>, Value<'_>)> = owned
        .iter()
        .flatten()
        .map(|owned| (owned.as_raw(), owned.as_raw().to_value().unwrap()))
        .collect();
    for (a, a_value) in &valid {
        for (b, b_value) in &valid {
            check_pair(*a, a_value, *b, b_value);
        }
    }
    let le = |x: &RawJsonb<'_>, y: &RawJsonb<'_>| x.partial_cmp(y) != Some(Ordering::Greater);
    for x in &valid {
        for y in &valid {
            for z in &valid {
                assert!(
                    !(le(&x.0, &y.0) && le(&y.0, &z.0)) || le(&x.0, &z.0),
                    "comparison is not transitive: {} <= {} <= {}",
                    x.1,
                    y.1,
                    z.1
                );
            }
        }
    }
}

/// Checks two valid values against each other.
fn check_pair(a: RawJsonb<'_>, a_value: &Value<'_>, b: RawJsonb<'_>, b_value: &Value<'_>) {
    let order = a.partial_cmp(&b).expect("valid values compare");
    assert_eq!(
        Some(order.reverse()),
        b.partial_cmp(&a),
        "comparison is not antisymmetric: {a_value} vs {b_value}"
    );
    assert_eq!(
        order,
        a_value.cmp(b_value),
        "RawJsonb and Value order differ: {a_value} vs {b_value}"
    );
    let encoded = a.convert_to_comparable().cmp(&b.convert_to_comparable());
    assert_comparable_order(order, encoded, || format!("{a_value} vs {b_value}"));

    let concat = model::concat(a_value, b_value);
    assert_model(a.concat(&b).ok(), Some(concat), || {
        format!("concat({a_value}, {b_value})")
    });
    let contains = a.contains(&b).unwrap();
    assert_eq!(
        contains,
        model::contains(a_value, b_value),
        "contains({a_value}, {b_value})"
    );
}
