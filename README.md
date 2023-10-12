# jsonb &emsp; [![Build Status]][actions] [![Latest Version]][crates.io] [![Crate Downloads]][crates.io]

[build status]: https://img.shields.io/github/actions/workflow/status/datafuselabs/jsonb/rust.yml?branch=main
[actions]: https://github.com/datafuselabs/jsonb/actions?query=branch%3Amain
[latest version]: https://img.shields.io/crates/v/jsonb.svg
[crates.io]: https://crates.io/crates/jsonb
[crate downloads]: https://img.shields.io/crates/d/jsonb.svg


`jsonb` is a binary format `JSON` representation inspired by [PostgreSQL](https://www.postgresql.org/docs/current/datatype-json.html) and [CockroachDB](https://www.cockroachlabs.com/docs/stable/jsonb). It provides a fast, lightweight and easy-to-use API for working with `JSON` data.

## Features

- Good compatibility: `jsonb` fully supports the `JSON` standard and can be used to store complex data structures.
- Fast performance: `jsonb` is designed for high performance, allowing you to work with large `JSON` data sets with ease.
- Easy to use: `jsonb` provides a number of built-in functions to support various operations, and also supports the `JSONPath` syntax for selecting and extracting subset elements.
- Safe and secure: `jsonb` is written in Rust, which provides memory and thread safety guarantees, making it a safe choice for handling sensitive data.

## Encoding format

The `jsonb` encoding format is a tree-like structure. Each node contains a container header, a number of JEntry headers, and nested encoding values.

- 32-bit container header. 3 bits identify the type of value, including `scalar`, `object` and `array`, and 29 bits identify the number of JEntries in the `array` or `object`. The root node of the `jsonb` value is always a container header.
  - `scalar` container header: `0x20000000`
  - `object` container header: `0x40000000`
  - `array` container header: `0x80000000`
- 32-bit JEntry header. 1 bit identifies whether the JEntry stores a length or an offset, 3 bits identify the type of value, including `null`, `string`, `number`, `false`, `true` and `container`, and the remaining 28 bits identify the length or offset of the encoding value.
  - `null` JEntry header: `0x00000000`
  - `string` JEntry header: `0x10000000`
  - `number` JEntry header: `0x20000000`
  - `false` JEntry header: `0x30000000`
  - `true` JEntry header: `0x40000000`
  - `container` JEntry header `0x50000000`
- Encoding value. Different types of JEntry header have different encoding values.
  - `null`, `true`, `false`: no encoding value, identified by the JEntry header.
  - `string`: a normal UTF-8 string.
  - `number`: an encoded number to represent uint64s, int64s and float64s.
  - `container`: a nested `json` value with a recursive structure.

#### An encoding example

```text
// JSON value
[false, 10, {"k":"v"}]

// JSONB encoding
0x80000003    array container header (3 JEntries)
0x30000000    false JEntry header (no encoding value)
0x20000002    number JEntry header (encoding value length 2)
0x5000000e    container JEntry header (encoding value length 14)
0x500a        number encoding value (10)
0x40000001    object container header (1 JEntry)
0x10000001    string key JEntry header (encoding value length 1)
0x10000001    string value JEntry header (encoding value length 1)
0x6b          string encoding value ("k")
0x76          string encoding value ("v")
```

## Jsonb value

The `jsonb` value is an enumeration that represents all kinds of `JSON` values and serves as an intermediate for converting other data types to the `jsonb` binary format value.

```rust
// jsonb value
#[derive(Clone, PartialEq, Eq)]
pub enum Value<'a> {
    Null,
    Bool(bool),
    String(Cow<'a, str>),
    Number(Number),
    Array(Vec<Value<'a>>),
    Object(Object<'a>),
}
```

## Built-in functions

`jsonb` implements a number of commonly used built-in functions. Since most functions only focus on a subset of the total value, using container headers and JEntry headers to can efficiently skip over intermediate parts of the `jsonb` value. This avoids time-consuming deserialisation operations and provides very high performance. For more information, see https://docs.rs/jsonb/latest/jsonb/#functions

## SQL/JSONPath

[SQL/JSONPath](https://www.iso.org/standard/67367.html) is a query language used to select and extract a subset of elements from a `jsonb` value.

#### Operators

The following operators have been implemented:

| Operator                 | Description                                                  | Examples           |
|--------------------------|--------------------------------------------------------------|--------------------|
| `$`                      | The root element                                             | `$`                |
| `@`                      | The current element in the filter expression                 | `$.event?(@ == 1)` |
| `.*`                     | Selecting all elements in an Object                          | `$.*`              |
| `.<name>`                | Selecting element that match the name in an Object           | `$.event`          |
| `:<name>`                | Alias of `.<name>`                                           | `$:event`          |
| `["<name>"]`             | Alias of `.<name>`                                           | `$["event"]`       |
| `[*]`                    | Selecting all elements in an Array                           | `$[*]`             |
| `[<pos>, ..]`            | Selecting 0-based `n-th` elements in an Array                | `$[1, 2]`          |
| `[last - <pos>, ..]`     | Selecting `n-th` element before the last element in an Array | `$[0, last - 1]`   |
| `[<pos1> to <pos2>, ..]` | Selecting all elements of a range in an Array                | `$[1 to last - 2]` |
| `?(<expr>)`              | Selecting all elements that matched the filter expression    | `$?(@.price < 10)` |

## Examples

```rust
fn main() {
    let json = r#"
        {
            "name":"Fred",
            "phones":[
                {
                    "type":"home",
                    "number":3720453
                },
                {
                    "type": "work",
                    "number":5062051
                }
            ]
        }"#;

    let path = r#"$.phones[*]?(@.number == 3720453)"#;

    // parse JSON string to jsonb value
    let value = jsonb::parse_value(json.as_bytes()).unwrap();
    // encode jsonb value to jsonb binary value
    let jsonb = value.to_vec();
    // parse JSONPath string
    let json_path = jsonb::jsonpath::parse_json_path(path.as_bytes()).unwrap();
    // select subset value from jsonb binary value
    let mut sub_jsonb = Vec::new();
    let mut sub_offsets = Vec::new();
    jsonb::get_by_path(&jsonb, json_path, &mut sub_jsonb, &mut sub_offsets);

    // value={"number":3720453,"type":"home"}
    println!("value={}", jsonb::to_string(&sub_jsonb));
}
```

## Contributing

`jsonb` is an open source project and all kinds of contributions are welcome! You can help with ideas, code or documentation.

## License

Licensed under the [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
