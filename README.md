# jsonb &emsp; [![Build Status]][actions] [![Latest Version]][crates.io] [![Crate Downloads]][crates.io]

[build status]: https://img.shields.io/github/actions/workflow/status/datafuselabs/jsonb/rust.yml?branch=main
[actions]: https://github.com/datafuselabs/jsonb/actions?query=branch%3Amain
[latest version]: https://img.shields.io/crates/v/jsonb.svg
[crates.io]: https://crates.io/crates/jsonb
[crate downloads]: https://img.shields.io/crates/d/jsonb.svg



`jsonb` is a jsonb implementation written in Rust. It provides a fast, lightweight, and easy-to-use API for working with jsonb data.

## Features

- Fast performance: `jsonb` is designed to be highly performant, allowing you to work with large jsonb data sets with ease.
- Easy to use API: `jsonb` provides a simple and intuitive API for working with jsonb data, making it easy to get started.
- Safe and secure: `jsonb` is written in Rust, which provides memory safety and thread safety guarantees, making it a safe choice for handling sensitive data.
- Flexible: `jsonb` supports a wide range of data types and can be used to store complex data structures.


## JSONB value struct

``` rust
// JSONB value
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

