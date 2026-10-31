# Shell Script Retirement Decision Log

## Context

Per project policy (~/.claude/CLAUDE.md and the debt audit
findings), .sh scripts under `bin/` and `scripts/` violate the
"no shell scripts in this Rust repo" rule. Phase 1 of the
remediation roadmap enumerates and classifies them; ports
happen in follow-up tasks.

Policy target: zero .sh files under `bin/` and `scripts/`.
The only exemptions permitted are third-party binaries (e.g.
micromamba) that must live under `vendor/`.

Task reference: P1.S4.T1 (inventory) and P1.S4.T2 (classify).

## Inventory (16 files as of 2026-04-17)

### Category A -- DELETE (trivial, replaceable by git commands)

Status: COMPLETE (2026-04-17). All four scripts removed from `bin/`.

| File                  | Lines | Decision | Rationale                                                       | Status             |
| --------------------- | ----- | -------- | --------------------------------------------------------------- | ------------------ |
| `bin/do_commit.sh`    | 2     | DELETE   | Hardcoded commit message; replaceable by `git commit -m "..."`. | DELETED 2026-04-17 |
| `bin/temp_commit.sh`  | 3     | DELETE   | Identical intent to do_commit.sh; obsoleted.                    | DELETED 2026-04-17 |
| `bin/build_fix.sh`    | 4     | DELETE   | One-line `cargo build` redirect; trivial.                       | DELETED 2026-04-17 |
| `bin/check_gemini.sh` | 14    | DELETE   | Debug helper from a past investigation; no ongoing use.         | DELETED 2026-04-17 |

### Category B -- PORT TO MAKEFILE TARGET

| File                                                       | Lines | Decision | Target Makefile name                                                |
| ---------------------------------------------------------- | ----- | -------- | ------------------------------------------------------------------- |
| `scripts/cargo_cache_prune.sh` | 24 | DONE | Removed; `make cargo-cache-prune` depends on `clean-builds`, which removes a superset of its trees. |
| `scripts/cargo_cache_status.sh` | 115 | DONE | Removed; `repo-utilities cargo-cache-status` prints the same report through `make cargo-cache-status`. |
| `scripts/docs-redirect-check.sh`                           | 104   | DONE     | Replaced by `repo-utilities docs-redirect-check` through `make docs-redirect-check`. |
| `scripts/run_nanograv_timing_phase1_independent_locked.sh` | 8 | DONE | Removed; `make nanograv-timing-phase1-independent` runs the same `cargo run` command. |

### Category C -- PORT TO RUST BINARY (non-trivial logic)

| File                                  | Lines | Decision | New crate/binary                                                                                  |
| ------------------------------------- | ----- | -------- | ------------------------------------------------------------------------------------------------- |
| `scripts/bootstrap_user_local_xdg.sh` | 199 | DONE | Removed; `xtask bootstrap-user-local-xdg` writes the same tree through `make bootstrap-user-local-xdg`. |
| `scripts/detect_native_blas.sh` | 49 | DONE | Removed; `repo-utilities native-blas` prints the same report through `make doctor-blas`. |
| `scripts/detect_physical_cores.sh`    | 5     | DONE     | Removed; host inspection remains available through `xtask host-profile`.                           |
| `scripts/detect_worker_budget.sh`     | 11    | DONE     | Removed; hosted CI compiles and executes the typed `detect-worker-budget` Rust utility.            |
| `scripts/profile_tensor_avt.sh` | 211 | DONE | Removed; `gororoba_cli_physics --bin tensor-avt-profile-orchestrator` runs the same capture sequence through `make profile-tensor-avt`. |
| `scripts/run_lambda_sweep.sh` | 100 | DONE | Removed; `gororoba_cli_physics --bin lambda-sweep` runs the same sweep. |
| `bin/run_reynolds_sweep.sh` | 17 | DONE | Removed; `gororoba_cli_physics --bin run_reynolds_sweep` runs the same three sizes, building `warp-gpu-experiment` through `cargo run --release` rather than invoking a prebuilt binary. |

### Category D -- PRESERVE UNDER vendor/

| File                           | Lines | Decision | Location                                                                                                                                       |
| ------------------------------ | ----- | -------- | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| `bin/run_quantum_container.sh` | 15 | DONE | Removed with `docker/Dockerfile`, the `docker-quantum-*` make targets and the REQ-QUANTUM requirement module; the container mounted a `src/` tree the repository no longer has. |

### Category E -- BINARY / NON-SCRIPT

| File             | Size     | Decision | Notes                                                                                                                                |
| ---------------- | -------- | -------- | ------------------------------------------------------------------------------------------------------------------------------------ |
| `bin/micromamba` | external | VENDOR   | Third-party binary; relocate to `vendor/` with `docs/toolchain/micromamba.md` capturing sha256. (Task from plan Appendix: P1.S4.T5.) |

## Execution plan (follow-up tasks)

Each category rolls into its own PR to keep diffs reviewable.

1. Category A deletions: single PR, 4 files removed.
2. Category B ports: one PR per script or batched per target area;
   requires the target Makefile rule to be authored first.
3. Category C ports: one PR per Rust binary; may span sprints
   because porting preserves behavior bit-for-bit.
4. Category D review: decision captured in a separate ADR.
5. Category E: vendor relocation + docs.

## Verification

After full retirement:

find bin scripts -name '*.sh' 2>/dev/null | wc -l # expect 0
ls vendor/ | grep -E 'micromamba|third-party' # expect presence
make docs-redirect-check # expect green

## Related plan tasks

- P1.S4.T1 (inventory) -- COMPLETE.
- P1.S4.T2 (classify) -- this document.
- P1.S4.T3 (port Cat B/C) -- pending; multi-PR.
- P1.S4.T4 (delete Cat A) -- pending; single PR.
- P1.S4.T5 (vendor Cat E) -- pending; single PR.

### Archived scripts

`archive/root_cleanup_2026-04-03/scripts/download_papers.sh` (arXiv fetch
loop) and `archive/root_cleanup_2026-04-03/tests/test_find_fermion_boson.sh`
(a `grep` over `crates/`) had no caller and are removed; git history keeps
their bytes.

### Python scripts

| File | Decision | Replacement |
| --- | --- | --- |
| `experiments/identifiability/identifiability_compiler.py` and its pytest file | DONE | `gororoba_cli_physics --bin identifiability-compiler`; its in-file tests reproduce the boundary fractions 0.264486 and 0.027178 to 1e-6. |
| `scripts/check_refs.py` | DONE | `gororoba_cli_data --bin check-refs` through `make ref-audit` and `make ref-audit-strict`. |
