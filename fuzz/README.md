# jsonb fuzz targets

Coverage-guided fuzzing with [cargo-fuzz] (libFuzzer + AddressSanitizer).

[cargo-fuzz]: https://github.com/rust-fuzz/cargo-fuzz

| Target | Input | Checks |
|---|---|---|
| `raw_jsonb` | Arbitrary bytes as JSONB | Every read/transform API; a value that decodes re-encodes to stable bytes and decodes back to an equal value |
| `json_text` | Arbitrary bytes as JSON text | All parsers and encoders agree byte for byte; `Value` and `RawJsonb` format the same valid JSON, which parses back to an equal value; standard mode accepts what `serde_json` accepts |
| `json_path` | Arbitrary bytes as a JSONPath, key path, or canonical key path | Evaluation against fixed documents; formatted paths parse back to the same path |
| `binary_ops` | Two or three values separated by `0x00`, each parsed as JSON text when possible | Two-value APIs; comparison is a total order that agrees with `Value::cmp` and is never reversed by `convert_to_comparable` |
| `number` | Two `Number`s of any variant | Arithmetic never returns a wrong integer and fails only on overflow; formatted numbers parse back to equal values |

Every target must run without panics, stack overflows, memory errors, or
allocations far larger than the input. For valid values, `src/model.rs` also
checks function results against simple reference implementations on `Value`.

## Running

cargo-fuzz needs a nightly toolchain. Set up once, from the repository root:

```sh
cargo install cargo-fuzz
cd fuzz
cargo run --bin write_seeds
```

`write_seeds` writes the seeds listed in `src/bin/write_seeds.rs` into
`corpus/<target>/`, one file per seed since libFuzzer reads each file as one
input. Besides typical inputs, the seeds hold the tokens and boundary values of
each format, so mutations can copy them. Add new seeds there. libFuzzer adds the
inputs it discovers to the same directory, which is git-ignored.

Then run one target at a time, from the `fuzz` directory:

```sh
# JSONB bytes
cargo +nightly fuzz run raw_jsonb -- -max_len=4096 -malloc_limit_mb=512 -timeout=10

# JSON text
cargo +nightly fuzz run json_text -- -max_len=4096 -malloc_limit_mb=512 -timeout=10

# JSONPath and key paths
cargo +nightly fuzz run json_path -- -max_len=1024 -malloc_limit_mb=512 -timeout=10

# Comparison, concat, and contains on two or three values
cargo +nightly fuzz run binary_ops -- -max_len=4096 -malloc_limit_mb=512 -timeout=10

# Number arithmetic; two numbers take at most 68 bytes
cargo +nightly fuzz run number -- -max_len=128 -malloc_limit_mb=512 -timeout=10
```

- `-max_len` caps the input size; larger inputs mostly slow the fuzzer down.
- `-malloc_limit_mb` turns any single allocation above the limit into a crash,
  catching lengths read from the input being trusted for allocation.
- `-timeout=10` reports inputs that run longer than 10 seconds; the default is
  20 minutes, so without it a hang looks like the fuzzer has gone quiet.
- Add `-fork=N -ignore_crashes=1` to fuzz on `N` processes and keep going after
  a crash, and `-max_total_time=<seconds>` to stop after a while.

libFuzzer prints only when it finds new coverage, so long quiet periods are
normal once coverage levels off.

Crashing inputs are written to `artifacts/<target>/`. To reproduce and shrink one:

```sh
cargo +nightly fuzz run raw_jsonb artifacts/raw_jsonb/crash-<hash>
cargo +nightly fuzz tmin raw_jsonb artifacts/raw_jsonb/crash-<hash>
```

When fixing a bug found this way, add the minimized input as a regression test
under `tests/it/`, which runs on stable with `cargo test`.

To see which code the corpus reaches:

```sh
cargo +nightly fuzz coverage raw_jsonb corpus/raw_jsonb
```
