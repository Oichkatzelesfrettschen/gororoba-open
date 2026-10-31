// SPDX-License-Identifier: MIT
//
// Validation-tool byte inspection: find compile-time paths from vanished
// worktrees inside the copied validation binaries. The cache and BLAS
// reports are host probes reachable from the `repo-utilities` binary, and
// `path_hygiene` holds the shrink-only rule for absolute home paths in
// tracked text.

pub mod cargo_cache;
pub mod native_blas;
pub mod path_hygiene;
pub mod validation_tool_paths;
