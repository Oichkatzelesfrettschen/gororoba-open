//! # Living Verification Artifact -- Pipeline Architecture
//!
//! ## Overview
//!
//! The LVA pipeline connects Rocq formal proofs to the LaTeX paper, ensuring
//! the PDF cannot desynchronize from the prover.
//!
//! ```
//! gororoba-math rocq/open: Rocq .v sources
//!     |
//!     v
//! sh ci/check_rocq.sh: compile -> .vo, kernel check, axiom ledger
//!     |
//!     +-> ci/kernel_replay_evidence.py -> replay evidence file
//!     |                                     |
//!     |                                     v (gororoba-db theorem identity
//!     |                                        record-kernel-evidence)
//!     |                               provenance_store theorem_replay::ingest
//!     |                                     |
//!     |                                     v
//!     |                               kernel receipt in the registry
//!     |
//!     +-> Extraction -> OCaml functor -> golden file diff
//!                                         |
//!                                         v (manual translation)
//!                                     verified_core/ (Rust crate)
//!                                         |
//!                                         v
//!                                     cross_validate.rs (Rust cross-check)
//! ```
//!
//! ## Where The Pipeline Runs
//!
//! The Rocq proof tree lives in the gororoba-math repository under
//! `rocq/open`; gororoba-open holds no `proofs/` tree and runs no Rocq. The
//! toolchain and the proof commands are described in `rocq/open/README.md`
//! there, its `Justfile` names the targets (`check`, `extract`, `all`), and
//! `sh ci/check_rocq.sh` in gororoba-math compiles and kernel-checks the tree
//! under Rocq 9.3.0.
//!
//! gororoba-open ingests the result as a replay evidence file that
//! `ci/kernel_replay_evidence.py` in gororoba-math writes, through
//! `gororoba-db theorem identity record-kernel-evidence`. When a proof source
//! imports Flocq, ingest requires the evidence file's Flocq object list to
//! equal the committed copy of `ci/flocq-manifest.json` in gororoba-math,
//! which names the objects of the producer's opam switch. The manifest
//! identifies one build of the opam export: a hosted runner that built the
//! same export produced different Flocq object bytes (measured; first
//! difference at `Calc/Bracket.vo`). This repository has no target for proof
//! metrics, dependency-graph figures or `rocq doc` output.
//!
//! ## Trust Boundary
//!
//! The trust boundary is the single point where abstract proofs meet concrete
//! IEEE 754 arithmetic:
//!
//! - **Rocq side**: `FLOAT_OPS` module type in `theories/FloatAxioms.v` --
//!   abstract field axioms (add_comm, mul_assoc, etc.)
//! - **Rust side**: `crates/verified_core/src/axioms.rs` -- maps each axiom
//!   to an `f64` primitive operation
//! - **Validation**: `crates/verified_core/tests/cross_validate.rs` -- sweeps
//!   36 rotation test cases at tolerance < 1e-12
//!
//! The axioms hold exactly for real numbers and approximately for f64. The
//! cross-validation confirms that rounding errors are negligible for the
//! quaternion rotation use case.
//!
//! ## Source Anchoring
//!
//! LaTeX code listings are pulled directly from source files using
//! `\inputminted` (from the `minted` package) with `firstline`/`lastline`
//! options. Tag comments in the source files mark the boundaries:
//!
//! - Rocq: `(*<*tagname>*) ... (*</tagname>*)`
//! - Rust: `//<*tagname> ... //</tagname>`
//!
//! NOTE: `catchfilebetweentags` was evaluated but its `%<*tag>` delimiter
//! format is incompatible with Rocq/Rust comment syntax. `\inputminted`
//! provides the same source-anchoring guarantee plus syntax highlighting.
//!
//! Tags in use (Rocq paths are relative to `rocq/open` in gororoba-math):
//!
//! | File | Tag | Content |
//! |------|-----|---------|
//! | `theories/FloatAxioms.v` | `floatops` | FLOAT_OPS module type |
//! | `theories/FloatQuaternion.v` | `quatrotate` | quat_rotate definition |
//! | `verified/C876_QuaternionRotation.v` | `c876rotation` | rotation = matrix theorem |
//! | `verified/C871_CasimirExact.v` | `c871cubic` | cubic scaling theorem |
//! | `theories/CayleyDicksonAlgebra.v` | `normconj` | norm-conjugate identity |
//! | `verified_core/src/axioms.rs` | `trustboundary` | f64 axiom realization |
//! | `verified_core/src/quaternion.rs` | `quatrotatefn` | quat_rotate function |
//! | `verified_core/tests/cross_validate.rs` | `crossval` | sweep test |
//!
//! ## Opam Environment
//!
//! - Switch: `rocq-9.3`, built by `ci/install_rocq.sh` in gororoba-math
//! - Rocq: 9.3.0 (OCaml 5.5.1)
//! - External Rocq dependencies: Flocq 4.2.2 (`coq-flocq`) and the plugin
//!   ports that `rocq/open/README.md` in gororoba-math lists
//!
//! ## Tool Versions
//!
//! | Tool | Version | Purpose |
//! |------|---------|---------|
//! | rocq | 9.3.0 | Proof compiler (gororoba-math) |
//! | latexmk | system | LaTeX build |
//! | dot2tex | 2.11.3 | DOT -> TikZ |
//! | pygmentize | 2.19.2 | Syntax highlighting (minted) |
//! | dot | system | Graph rendering |
//!
//! ## Known Limitations
//!
//! - **Alectryon**: BLOCKED. SerAPI not ported to Rocq 9.x. Using `rocq doc`
//!   as fallback for HTML documentation.
//! - **coq-dpdgraph**: SKIPPED. Forces rocq-stdlib 9.1.0 -> 9.0.0 downgrade,
//!   breaking `From Stdlib Require Import` namespace. Using file-level
//!   dep_graph.sh + dot2tex instead.
//! - **arXiv**: Does not support `--shell-escape` (required by minted). The
//!   arXiv version should use `listings` package instead.
//! - **verified_core scope**: Currently covers only quaternion rotation (1 of
//!   ~40 gr_core modules). Expansion to ADM, Casimir, and energy conditions
//!   is future work.
//! - **rocq-rust-extraction 0.2.0**: Evaluated and DEFERRED. Extracts Records
//!   as Rust enums (not structs), uses lifetime-heavy `&'a` style with
//!   `PhantomData`, and does not map Module Types to Rust traits. Our manual
//!   translation in verified_core is simpler and more idiomatic for numerical
//!   f64 code. Re-evaluate when the tool supports struct extraction and trait
//!   mapping from abstract module types.
//! - **Proof checking**: gororoba-math checks the proofs (`ci/check_rocq.sh`);
//!   gororoba-open runs no Rocq lane.
//!
