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
