# Benchmarks

The benches use [criterion](https://docs.rs/criterion). Run them from the
repository root.

| Bench | What it measures |
|---|---|
| `read` | Parsing JSON text into JSONB and reading JSONB: `parse_owned_jsonb`, `from_slice`, `to_value`, `to_string`, `from_raw_jsonb`, `object_each`, `get_by_name`, `select_by_path`, `contains`, `partial_cmp`, `convert_to_comparable`, `strip_nulls` |
| `write` | Building and modifying JSONB, and encoding other values as JSONB: `build_array`, `object_insert`, `array_insert`, `concat`, `delete_by_name`, `select_array_by_path($.**)`, `to_owned_jsonb(serde_json)`, `Value::to_vec`, `OwnedJsonb::try_from(jaq)` |
| `array` | `array_distinct`, `array_intersection`, `array_except` and `array_overlap`, each array taken against itself |
| `json_path` | `parse_json_path` on a simple path, filters with 1 to 256 `&&`/`||` operators, and a field name that contains `&&` |
| `parser` | Parsing JSON text with jsonb, serde_json, json-deserializer and simd-json |
| `get_path` | Looking up a value by path in jsonb and in `serde_json::Value` |
| `strip_nulls` | `strip_nulls` on JSONB, and the same through `Value` |

`read`, `write` and `array` run every operation on four documents:
`data/canada.json` (mostly numbers), `data/citm_catalog.json` (mostly
objects), `data/twitter.json` (mostly strings), and a 162-byte object defined
in `common/mod.rs`, which also holds the paths and keys each document is queried
with. `contains` skips canada: array containment is quadratic, and one call
takes about 36 s.

## Running

```sh
# Every bench. `read`, `write`, `array` and `json_path` alone take about
# 10 minutes together.
cargo bench

# One bench.
cargo bench --bench read

# Only the benchmarks whose ID matches a regular expression. IDs are
# `<document>/<operation>`, or `parse_json_path/<case>` for `json_path`.
cargo bench --bench read -- canada/to_string
cargo bench --bench read -- 'twitter/(to_value|to_string)'

# Run each benchmark once without measuring, to check that they all work.
cargo bench --bench read -- --test
```

Criterion prints each result and writes an HTML report to
`target/criterion/report/index.html`.

On the large documents an operation takes milliseconds, so those benchmarks
take 20 flat samples over 3 s after 1 s of warm-up. The small object and
`json_path` use criterion's defaults: 100 samples over 5 s after 3 s of
warm-up.

## Measuring with Databend's build settings

Databend builds jsonb with `opt-level = "s"`, `codegen-units = 1` and
`lto = "thin"`, which can rank changes differently from the default bench
profile (`opt-level = 3`). To measure what Databend runs, set the same values
for the bench profile:

```sh
CARGO_PROFILE_BENCH_OPT_LEVEL=s \
CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 \
CARGO_PROFILE_BENCH_LTO=thin \
cargo bench --bench read
```

## Comparing two versions

Save the results of the old version as a named baseline, then run the new
version against it. Criterion reports the change of each benchmark and whether
it is significant.

```sh
cargo bench --bench read -- --save-baseline before   # on the old version
cargo bench --bench read -- --baseline before        # on the new version
```

To keep your working tree untouched, build the old version in a separate
worktree:

```sh
git worktree add ../jsonb-before <old-commit>
cp Cargo.lock ../jsonb-before/
export CRITERION_HOME="$PWD/target/criterion"
(cd ../jsonb-before && cargo bench --bench read -- --save-baseline before)
cargo bench --bench read -- --baseline before
git worktree remove ../jsonb-before
```

Keep these the same on both sides, or the comparison measures them instead of
the code:

- **Benches.** Both versions need the bench files and their `[[bench]]`
  entries in `Cargo.toml`. For a commit older than these benches, copy
  `benches/` and the entries over; older APIs may need small edits, for
  example `Value::to_vec` returned `Vec<u8>` instead of `Result`.
- **`Cargo.lock`.** It is not committed, so each checkout resolves its own
  dependency versions. Newer `itoa`, `zmij` or `fast-float2` releases alone
  change number formatting and parsing by several percent.
- **Baseline directory.** Criterion keeps baselines in `$CRITERION_HOME`, or
  else in `criterion/` under the Cargo target directory. Point both runs at
  one directory, as `CRITERION_HOME` does above.
- **Build settings.** Use the same profile variables for both runs.

Results move by a few percent between runs, and a change elsewhere in the
crate can move a benchmark by several percent through code layout alone.
Rerun a benchmark before trusting a small change, and check large ones
against the other documents.
