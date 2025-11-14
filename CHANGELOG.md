## [v0.5.5] - 2025-11-17

### Added

- Feat: Support function `extract_scalar_key_values` (#95)
- Feat: Make JsonbItemType public so users can compare (#94)

### Fixed

- Fix: fix `serde_json` infinite Number convert to Jsonb Value unwrap panic (#96)

## [v0.5.4] - 2025-08-20

### Added

- Feat: Support parse extended json5 syntax (#92)

## [v0.5.3] - 2025-08-02

### Added

- Perf: Improve parse json performance (#90)
- Chore: add toplevel feature to allow users to better manager dependencies (#89)

## [v0.5.2] - 2025-06-27

### Added

- Feat: Enhanced JSONB Parser with Decimal Support and Extended Syntax (#86)
- Feat: Support extension types (#83)

## [v0.5.1] - 2025-04-18

### Added

- Chore: Bump nom 8.0.0 (#84)

## [v0.5.0] - 2025-04-15

### Added

- Feat: json path support recursive wildcard member accessor `.**` syntax (#81)
- Refactor: get object value by key name improve performance (#79)
- Refactor: Implements serde trait for RawJsonb (#77)
- Refactor JSONB functions: Improved API, Documentation, and Data Structures (#75)
- Feat: add arithmatic expression support (#71)
- Feat(expr): add filter expr `starts with` (#52)

## [v0.4.4] - 2024-11-16

### Fixed

- Fix: panic when facing corrupted jsonb (#67)

### Added

- Bump fast-float2 v0.2.3  (#69)
- Feat: add a function to parse jsonb only (#66)
- Feat: support `object_delete` and `object_pick` function (#65)
- Feat: support `object_insert` function (#64)
- Feat: Support json array functions (#62)
- Feat: add lazy value (#61)

## [v0.4.3] - 2024-09-30

### Fixed

- Fix: Fix compare object value with different length panic (#59)

## [v0.4.2] - 2024-09-19

### Added

- Feat: make `preserve_order` a default feature (#56)

## [v0.4.1] - 2024-07-18

### Fixed

- Fix: Fix jsonpath selector unwrap panic. (#53)

## [v0.4.0] - 2024-05-17

### Fixed

- Fix: Fix get by keypath with null value. (#47)
- Fix: Handle invalid jsonb value to avoid panic in functions. (#46)
- Fix: Fix builder & concat container jentry len. (#43)

### Added

- Feat: Support convert jsonb value to `serde_json` value. (#49)
- Feat: Add `exists` filter expression. (48)`
- Feat: Add `delete_by_keypath`. (#45)
- Feat: Add `delete_by_index` & `delete_by_name`. (#44)
- Feat: Add `concat` & improve `strip_nulls`. (#42)
- Feat: Add jsonpath predicate support. (#41)
- Feat: Add `contains` api. (#40)
- Feat: Add `exists_any_keys` & `exists_all_keys`. (#38)
- Feat: Support parse key paths. (#37)
- Feat: Add `get_by_keypath`. (#36)

## [v0.3.0] - 2023-10-13

### Added

- Docs: Add more jsonb encoding format descriptions. (#34)
- Feat: Support `object_each` api. (#33)
- Feat: Support `path_exists` api. (#32)
- Feat: Support `type_of` api. (#31)
- Feat: Support `strip_nulls` api. (#30)
- Perf: Add benches for parser and `get_path`. (#29)
- Chore: Add check fmt and clippy. (#27)
- Feat: Support `to_pretty_string` api. (#26)
- Feat: Support `traverse_check_string` function. (#25)
- Feat: Improve json path selector using less memory. (#24)

## [v0.2.3] - 2023-07-10

### Fixed

- Fix: fix parse json path name with escaped characters. (#21)
- Fix: Fix some special characters display errors. (#18)
- Fix: Support parsing Unicode characters enclosed in brackets. (#17)
- Fix: json `to_string` function adds backslash for escaped characters. (#16)
- Fix: fix parse UTF-8 characters. (#15)

### Added

- chore: implement From trait with owned JsonValue for Value. (#22)
- Feat: Add function `convert_to_comparable`, `rand_value`. (#20)
- Create publish.yaml. (#19)

## [v0.2.2] - 2023-05-06

### Fixed

- Fix: Allow parse escaped white space. (#14)

## [v0.2.1] - 2023-05-05

### Fixed

- Fix: Allow parse invalid Unicode. (#13)

## [v0.2.0] - 2023-04-21

### Added

- Feat: Support `JSON path` selector. (#8)
- Feat: Support parse `JSON path` syntax. (#7)

## [v0.1.1] - 2023-03-03

- Rename project name to jsonb.
- Add Readme description. (#4)
- Use stable Rust. (#3)

## v0.1.0 - 2023-03-03

- Implement a `JSON` parser.
- Implement `JSONB` encodes and decodes.
- Implemented a number of `JSONB` functions.

[v0.5.5]: https://github.com/databendlabs/jsonb/compare/v0.5.4...v0.5.5
[v0.5.4]: https://github.com/databendlabs/jsonb/compare/v0.5.3...v0.5.4
[v0.5.3]: https://github.com/databendlabs/jsonb/compare/v0.5.2...v0.5.3
[v0.5.2]: https://github.com/databendlabs/jsonb/compare/v0.5.1...v0.5.2
[v0.5.1]: https://github.com/databendlabs/jsonb/compare/v0.5.0...v0.5.1
[v0.5.0]: https://github.com/databendlabs/jsonb/compare/v0.4.4...v0.5.0
[v0.4.4]: https://github.com/databendlabs/jsonb/compare/v0.4.3...v0.4.4
[v0.4.3]: https://github.com/databendlabs/jsonb/compare/v0.4.2...v0.4.3
[v0.4.2]: https://github.com/databendlabs/jsonb/compare/v0.4.1...v0.4.2
[v0.4.1]: https://github.com/databendlabs/jsonb/compare/v0.4.0...v0.4.1
[v0.4.0]: https://github.com/databendlabs/jsonb/compare/v0.3.0...v0.4.0
[v0.3.0]: https://github.com/databendlabs/jsonb/compare/v0.2.3...v0.3.0
[v0.2.3]: https://github.com/databendlabs/jsonb/compare/v0.2.2...v0.2.3
[v0.2.2]: https://github.com/databendlabs/jsonb/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/databendlabs/jsonb/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/databendlabs/jsonb/compare/v0.1.1...v0.2.0
[v0.1.1]: https://github.com/databendlabs/jsonb/compare/v0.1.0...v0.1.1
