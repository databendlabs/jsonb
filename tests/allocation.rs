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

//! Checks that work on untrusted input allocates in proportion to the input,
//! not to the lengths it claims or to how often a value is reused. This is a
//! separate test binary because it installs a global allocator that records
//! allocation sizes.

use std::alloc::GlobalAlloc;
use std::alloc::Layout;
use std::alloc::System;
use std::cell::Cell;

use jsonb::jsonpath::parse_json_path;
use jsonb::*;

struct RecordSizes;

thread_local! {
    // Per thread, so tests running in parallel do not see each other's
    // allocations. Constant-initialized cells never allocate themselves.
    static LARGEST: Cell<usize> = const { Cell::new(0) };
    static TOTAL: Cell<usize> = const { Cell::new(0) };
}

// SAFETY: forwards every call to `System` unchanged; it only records sizes.
unsafe impl GlobalAlloc for RecordSizes {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = layout.size();
        LARGEST.with(|largest| largest.set(largest.get().max(size)));
        TOTAL.with(|total| total.set(total.get() + size));
        // SAFETY: the caller upholds `GlobalAlloc::alloc`'s contract.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` was allocated by `System` with this `layout`.
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: RecordSizes = RecordSizes;

/// Runs `f` and returns the largest single allocation it made.
fn largest_allocation(f: impl FnOnce()) -> usize {
    LARGEST.with(|largest| largest.set(0));
    f();
    LARGEST.with(Cell::get)
}

/// Runs `f` and returns the total size of the allocations it made.
fn total_allocation(f: impl FnOnce()) -> usize {
    TOTAL.with(|total| total.set(0));
    f();
    TOTAL.with(Cell::get)
}

#[test]
fn claimed_lengths_do_not_size_allocations() {
    // JSON text read as JSONB: `[` is an object header claiming about 457
    // million entries, which used to reserve 7.3 GB before reading any of them
    // (found in review). The binary headers claim 2^29 - 1 entries.
    let inputs: [&[u8]; 5] = [
        b"[1,2,3]",
        br#"["a",{"b":null}]"#,
        br#""hello world""#,
        &0x9FFF_FFFF_u32.to_be_bytes(),
        &0x5FFF_FFFF_u32.to_be_bytes(),
    ];
    for input in inputs {
        let raw = RawJsonb::new(input);
        let largest = largest_allocation(|| {
            let _ = from_slice(input);
            let _ = raw.to_value();
            let _ = raw.to_string();
            let _ = from_raw_jsonb::<serde_json::Value>(&raw);
            let _ = serde_json::to_string(&raw);
            let _ = (raw.array_length(), raw.object_keys(), raw.array_values());
            let _ = (
                raw.object_each(),
                raw.strip_nulls(),
                raw.convert_to_comparable(),
            );
        });
        assert!(largest < 64 * 1024, "{input:?}: allocated {largest} bytes");
    }

    // Text that is not valid JSONB still parses as JSON text.
    assert_eq!(from_slice(b"[1,2,3]").unwrap().to_string(), "[1,2,3]");
}

#[test]
fn json_path_comparisons_do_not_copy_literals() {
    // A 100 KiB literal with an escape is stored as an owned string. Every
    // comparison used to clone it, so comparing 2000 strings against it
    // allocated about 200 to 600 MiB, outside the copy budget (found in review).
    let doc: OwnedJsonb = format!("[{}]", vec![r#""x""#; 2000].join(","))
        .parse()
        .unwrap();
    let literal = format!(r"\n{}", "a".repeat(100 * 1024));
    for path in [
        format!(r#"$[*] ? (@ == "{literal}")"#),
        format!(r#"$[*] ? (@ starts with "{literal}")"#),
        format!(r#"$ ? ($[*] == "{literal}")"#),
    ] {
        let path = parse_json_path(path.as_bytes()).unwrap();
        let mut selected = None;
        let total = total_allocation(|| {
            selected = Some(doc.as_raw().select_by_path(&path).map(|v| v.len()));
        });
        assert_eq!(selected, Some(Ok(0)));
        assert!(total < 1024 * 1024, "allocated {total} bytes");
    }
}
