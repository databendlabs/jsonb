## [v0.4.3] - 2024-09-30

### Fixed
Fix: Fix compare object value with different length panic (#59)

## [v0.4.2] - 2024-09-19

### Added
Feat: make `preserve_order` a default feature (#56)

## [v0.4.1] - 2024-07-18

### Fixed
Fix: Fix jsonpath selector unwrap panic. (#53)

## [v0.4.0] - 2024-05-17

### Fixed

Fix: Fix get by keypath with null value. (#47)
Fix: Handle invalid jsonb value to avoid panic in functions. (#46)
Fix: Fix builder & concat container jentry len. (#43) 

### Added

Feat: Support convert jsonb value to `serde_json` value. (#49) 
Feat: Add `exists` filter expression. (48)` 
Feat: Add `delete_by_keypath`. (#45)
Feat: Add `delete_by_index` & `delete_by_name`. (#44)
Feat: Add `concat` & improve `strip_nulls`. (#42)
Feat: Add jsonpath predicate support. (#41) 
Feat: Add `contains` api. (#40) 
Feat: Add `exists_any_keys` & `exists_all_keys`. (#38) 
Feat: Support parse key paths. (#37)
Feat: Add `get_by_keypath`. (#36)

## [v0.3.0] - 2023-10-13

### Added

Docs: Add more jsonb encoding format descriptions. (#34)
Feat: Support `object_each` api. (#33)
Feat: Support `path_exists` api. (#32)
Feat: Support `type_of` api. (#31)
Feat: Support `strip_nulls` api. (#30)
Perf: Add benches for parser and `get_path`. (#29)
Chore: Add check fmt and clippy. (#27)
Feat: Support `to_pretty_string` api. (#26)
Feat: Support `traverse_check_string` function. (#25)
Feat: Improve json path selector using less memory. (#24)

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


[v0.2.2]: https://github.com/datafuselabs/jsonb/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/datafuselabs/jsonb/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/datafuselabs/jsonb/compare/v0.1.1...v0.2.0
[v0.1.1]: https://github.com/datafuselabs/jsonb/compare/v0.1.0...v0.1.1
