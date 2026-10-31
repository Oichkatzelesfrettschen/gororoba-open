---
description: Shared build-dir, validation-tool identity, and cache budget for linked worktrees
last_verified: 2026-10-30
status: active
---

# Worktree build cache

Root `AGENTS.md` carries the prohibitions; this document carries the mechanics
of the shared build cache, the validation-tool identity stamp, and the cache
budget.

## Target directory and budget

- Default target dir for repository validation:
  `CARGO_TARGET_DIR="$(pwd)/.cache/gate-target"`. The physical path is retained
  for cache compatibility; the logical workflow uses `validate-*` targets.
  Pass it absolute. Cargo resolves a relative `CARGO_TARGET_DIR` against the
  shell's working directory, so a build launched from inside the tree writes a
  nested `.cache/gate-target/debug/.cache/gate-target`, exits 0, and leaves
  every later `stat` on the original path reading a stale artifact. The
  `Makefile` is already safe: `REPO_CARGO_TARGET_DIR` is
  `$(CURDIR)/.cache/gate-target`.
- Per-worktree experimental dirs: `.cache/exp-<name>-target/`.
- Cache budget: `make cache-check` enforces a soft cap of 150 GB
  (`CACHE_CHECK_SOFT_MB`, default 153600) and a hard cap of 250 GB
  (`CACHE_CHECK_HARD_MB`, default 256000) on `.cache/`; the Makefile defaults
  are authoritative. Sweep with `make cache-sweep` (cargo-sweep
  --maxsize 100GB) or `make cache-sweep-soft` for the soft cap.
- An isolated worktree on a capacity-constrained filesystem MUST set
  `REPO_CARGO_HOME`, `REPO_CARGO_TARGET_DIR`, and `REPO_CARGO_BUILD_DIR` to
  distinct paths on a filesystem that satisfies the cache budget.
- A linked worktree that explicitly builds a focused developer target on the
  same filesystem as the primary checkout SHOULD set
  `REPO_SHARE_PRIMARY_CACHE=1`. The roots are
  resolved in `mk/cache_roots.mk`: the cargo-home and the Cargo
  build-dir are shared with the primary checkout, while the target-dir,
  the validation-tools copies and cache-check sentinel stay under the
  worktree's own `.cache/`. The
  build-dir carries the dependency artifacts and is the path the
  sccache hash covers, so sharing it alone turns a cold ~70 min chain
  into ~10 min; keeping the target-dir local means a worktree with
  divergent tool sources never executes another worktree's `xtask` or
  governance binaries. Cargo keys a workspace crate on its content, so
  a byte-identical crate compiled in one worktree is handed to every
  other worktree through the shared build-dir; a tool therefore MUST
  NOT locate the repository through `env!("CARGO_MANIFEST_DIR")`,
  which bakes in the compiling checkout. `repo_root::resolve!()` and
  `repo_root::path!()` read `GOROROBA_REPO_ROOT` (exported by the
  Makefile as `$(CURDIR)`), then walk up from the working directory,
  and fall back to the compile-time path only when both fail. The
  owner is verified as a standard `<checkout>/.git` directory holding a
  `Cargo.toml`; bare, separate-git-dir and submodule layouts are
  rejected and need an explicit absolute `REPO_CACHE_OWNER`. Cleanup
  targets pass every path through `guarded_rm`, which refuses the
  owner's tree from a worktree unless `REPO_ALLOW_SHARED_CLEAN=1`.
  `make print-cache-roots` shows the resolved paths and
  `xtask/tests/cache_roots.rs` pins the layouts.

## Validation-tool identity

- The validation-tool cache identity is a sha256 over three inputs: the
  content hash of every `.rs` and `Cargo.toml` under `crates/` and `xtask/`,
  the resolved real path of the running checkout, and the git common-dir
  owner. `mk/cache_roots.mk` names the stamp
  `<validation-tools>/tool-identity.<identity>` and writes
  `tool_identity=`, `source_identity=`, `curdir_real=` and `owner=` into it.
  Two worktrees of one owner carry identical tool sources, so the source hash
  alone rates them equal; the checkout path is the term that separates them,
  and a stamp written for one worktree therefore never satisfies another.
- The identity gates the rebuild decision, not the bytes. Cargo keys a
  workspace crate on content and the shared build-dir hands one worktree's
  compiled crate to every other, so a fresh stamp can still stage a binary
  whose DWARF comp_dir strings name the compiling checkout. The staging step
  (`stage_tool` in the Makefile) strips debug sections from every copy, and
  because workspace sources are compiled by relative path the absolute
  checkout paths that survive are compile-time bake-ins such as
  `env!("CARGO_MANIFEST_DIR")`. `make validation-tools-check-paths` reads each
  staged file and fails on an absolute path under `$(REPO_WORKTREES_ROOT)`
  (default `$(HOME)/worktrees`) that names neither the running checkout nor a
  directory any live entry accounts for.
  `make validation-tools-check-paths` performs this explicit maintenance
  check. Repository validation itself runs from a fresh GitHub checkout.
- `make validation-tools-rebuild` discards every staged binary, stamp and
  identity file through `guarded_rm`, rebuilds through the `validation-tools`
  lane, and reruns the path scan. The cache-check sentinel stays in place.
  The rebuild also runs `cargo clean` over the tool
  packages and `repo_root`, because discarding the copy alone leaves Cargo
  free to answer the next build from the shared build-dir with the artifact
  another worktree compiled. Use it when a staged tool fails on a path from a
  checkout that no longer exists.

- Local sccache is host configuration, not a repository guarantee.
  `.cargo/config.toml` names it as the rustc wrapper; its cache size
  and location live in `~/.config/sccache/config`. A cache at its size
  ceiling evicts entries between sessions, so a gate tree of tens of
  GiB needs a ceiling above the tree size (48 GiB on the reference
  host).
