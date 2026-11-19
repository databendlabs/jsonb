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

//! Helpers shared by the test modules.

use jsonb::OwnedJsonb;

/// Runs `f` on a thread with a large stack.
///
/// Debug builds use up to ~9 KiB of stack per nesting level, so walking
/// `MAX_DEPTH` levels needs more than the test harness's default 2 MiB.
pub(crate) fn with_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// Builds `[[...[]...]]` with `depth` arrays, using the public builder.
pub(crate) fn nested_arrays(depth: usize) -> OwnedJsonb {
    let mut cur = "[]".parse::<OwnedJsonb>().unwrap();
    for _ in 1..depth {
        cur = OwnedJsonb::build_array([cur.as_raw()]).unwrap();
    }
    cur
}

/// Runs `f` on its own thread and fails if it does not finish within 10 seconds.
pub(crate) fn within_timeout<T: Send + 'static>(
    name: &str,
    f: impl FnOnce() -> T + Send + 'static,
) -> T {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || tx.send(f()).unwrap());
    rx.recv_timeout(std::time::Duration::from_secs(10))
        .unwrap_or_else(|_| panic!("{name} did not finish within 10 seconds"))
}
