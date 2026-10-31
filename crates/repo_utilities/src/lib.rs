// SPDX-License-Identifier: MIT
//
// Validation-tool byte inspection: find compile-time paths from vanished
// worktrees inside the copied validation binaries. The cache and BLAS
// reports are host probes reachable from the `repo-utilities` binary.

pub mod cargo_cache;
pub mod native_blas;
pub mod validation_tool_paths;
