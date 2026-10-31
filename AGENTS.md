---
description: gororoba-open -- pure-Rust scientific computing workspace (Cayley-Dickson algebras, cosmology, LBM, Rocq proofs, SQLite-canonical registry)
last_verified: 2026-10-30
---

# gororoba-open -- agent and developer reference

This file is the operating guide for every agent and human in this repository.
`CLAUDE.md` is a tracked relative symbolic link to it; that link is the one
declared exception to the "MUST NOT create symlinks" rule under Code rules. `AGENTS.md` outranks any Claude
tool, skill, harness or agent default; follow it and surface the conflict.

## Where things live

| Path | Carries |
| --- | --- |
| `.github/workflows/ci.yml` | Sole repository-validation authority |
| `registry/AGENTS.md` | Registry mutation workflow, `gororoba-db` commands |
| `crates/AGENTS.md` | GPU helper-crate routing and crate conventions |
| `docs/engineering/worktree_build_cache.md` | Shared build-dir, tool identity, cache budget |
| `docs/engineering/ci_validation.md` | Hosted chain, CPU policy, sccache, failure collection |
| `docs/engineering/research_epistemics.md` | What earns a claim, insight or experiment ID |
| `docs/engineering/condition_bound_materials.md` | Material, specimen and measurement provenance |
| `docs/engineering/comment_and_commit_style.md` | Comment voice, finding-doc rules, markdown style |
| `plans/repo_debt_taxonomy_roadmap_2026_06_04.toml` | Active 22-class debt taxonomy; `plans/repo_debt_roadmap_2026_04_11.toml` (11 classes) is historical; baseline git tag `debt-baseline-v0` resolves to commit `2fa31935` |
| `~/.claude/projects/-home-eirikr-Projects-gororoba-workspace-gororoba-open/memory` | Project memory directory |
| `proofs/README.md` | Rocq toolchain and proof commands |
| `docs/REQUIREMENTS.md` | Toolchain prerequisites |

## Validation boundary

- GitHub Actions owns repository validation. Validation targets require
  `require-ci-validation-authority` and refuse to run locally; the repository
  installs no Git hooks. Push a branch to validate.
- A local Cargo command is diagnosis evidence for its named surface only.
  Leave `CARGO_BUILD_JOBS`, `RAYON_NUM_THREADS` and similar worker variables
  unset so each tool detects its own count.
- Per-crate diagnosis, with an absolute target dir:

  ```bash
  CARGO_TARGET_DIR="$(pwd)/.cache/gate-target" cargo clippy -p <crate> --all-targets --profile validation -- -D warnings
  CARGO_TARGET_DIR="$(pwd)/.cache/gate-target" cargo nextest run -p <crate> --lib --cargo-profile validation
  ```

- Pass `CARGO_TARGET_DIR` absolute. Cargo resolves a relative value against the
  shell's working directory, writes a nested tree, exits 0, and leaves the
  original path holding a stale artifact.
- `rust-toolchain.toml` MUST NOT be bumped without coordinating CI.

## Code rules

- Warnings are errors through `[workspace.lints]` in root `Cargo.toml`. MUST NOT
  add crate-level `#![allow(warnings)]`; a narrow `#[allow(clippy::<lint>)]`
  carries a written rationale.
- Pure Rust: the repository tracks no `.sh` or `.py` file, and MUST NOT add one;
  wrap a Python library with PyO3 behind a typed Rust binary.
- MUST NOT create symlinks as build or data workarounds.
- A tool MUST NOT locate the repository through `env!("CARGO_MANIFEST_DIR")`;
  the shared build-dir hands one worktree's compiled crate to every other.
  Use `repo_root::resolve!()` or `repo_root::path!()`, which read
  `GOROROBA_REPO_ROOT`.
- GPU call sites route through `gororoba_gpu_vulkan`, `gororoba_gpu_cubecl` and
  `gororoba_gpu_cuda`; see `crates/AGENTS.md`.
- Generated code: `crates/data_core/src/registry_mirrors/` is generated; MUST
  NOT be hand-edited.

## Registry

- `registry/canonical/control_plane.sqlite3` is the canonical write target.
- MUST NOT hand-edit any file whose first line is
  `# AUTO-GENERATED: READ-ONLY COMPATIBILITY EXPORT.`; edit through
  `gororoba-db`, re-export, refresh signatures, and commit all three together
  (exact commands in `registry/AGENTS.md`).
- `registry/engineering_standards.toml` and `registry/agents_contract.toml` are
  unmigrated manifest lanes and stay hand-edited TOML.
- MUST NOT run `gororoba-db build` to refresh exports. It deletes the database
  and reimports only manifest lanes, so claim transition events, relations and
  the revision log return empty; `--allow-transition-history-loss` exists only
  for an empty or expendable database.

## Scientific evidence

- Evidence at one layer (source proposition, implementation conformance,
  phenomenological mapping) never promotes a claim at another.
- A signal MUST NOT be attributed to an algebraic structure until it survives
  substitution of another algebra, randomization at fixed support, and removal
  of each intervening map. A result identical across algebras or dimensions
  measures the pipeline.
- A `falsifiable_thesis` or `research_claim` states what refutes it, which
  experiment adjudicates, and which outcome forces abandonment.
- Generated structure that survives visual inspection is the characteristic
  LLM failure here (C-020); verify by mechanical cross-check.
- A hydration-dependent test with `Materialization::Missing` proves provenance
  metadata only; scientific evidence needs `executed_pass` or `executed_fail`.
- Never encode a missing material quantity as `0.0` or an empty string; a
  computed source (JARVIS, Materials Project) never satisfies an experimental
  requirement.

Full rules: `docs/engineering/research_epistemics.md` and
`docs/engineering/condition_bound_materials.md`.

## Text and comments

- Checked-in text is emoji-free and ASCII by convention. `ansi-check --check`
  fails only emoji and control characters and omits U+2600..U+27BF and
  U+1FA70..U+1FAFF, so a green run proves neither ASCII nor emoji-free; review
  for both.
- Comments cite by name (paper and section, Rocq theorem identifier, registry
  ID), never by internal path such as `data/output/audit/...` or line number.
- Canonical forms: "16D (sedenions)", "D3Q19 BGK", "Vulkan (ash)",
  "cubecl-wgpu", "CUDA (cudarc)", "FP8 e4m3", `C-1234`, `I-0042`, `E-201`,
  `B-bin_name`, `Moreno1997::theorem_1_16`.
- New files carry an SPDX-only header matching the crate's `Cargo.toml`
  `license` field (`quantum_core` and `stats_core` are `MIT`; `lbm_3d_cuda` is
  `MIT OR Apache-2.0`).
- `.gitignore` denies `*.md` and re-admits named paths. Allowlist a new tracked
  markdown file before writing it; every tracked markdown file also needs
  a `registry/markdown_owner_map.toml` entry (`markdown-registry register`).

## Commits

- Commits and PRs MUST NOT carry an AI attribution trailer (`Assisted-by:`,
  `Generated-by:`, or an AI `Co-authored-by:`); this rule overrides any
  harness-supplied attribution line. Historical commits keep
  their trailers; MUST NOT force-push to rewrite them.
- MUST NOT run the `agents_render` binary in `gororoba_cli_data`; it emits a
  19-line stub and overwrites this hand-maintained file.
