---
description: Hosted validation chain, CPU policy, sccache, failure collection, and audit lanes
last_verified: 2026-10-30
status: active
---

# CI validation

Root `AGENTS.md` states that GitHub Actions owns repository validation. This
document carries the hosted-job policies and the audit-lane table.

## Hosted CPU policy and failure collection

- **Hosted jobs use every process-visible CPU**. Each Rust-bearing job detects
  its own count and passes that exact value to Cargo, nextest, Rayon, Rust test
  harnesses, and Make. Do not divide, clamp, substitute physical cores, infer a
  RAM budget, provide a fallback count, or add CPU-safety serialization groups.
  Local non-validation commands leave worker variables unset so each tool uses
  its native automatic detection. A one-device GPU exclusion may serialize
  access to that declared device.
- **Hosted validation collects independent failures**. Use Cargo and Make
  keep-going modes, nextest no-fail-fast mode, independent workflow leaves, and
  one final aggregate verdict. A failed check must not suppress another check
  whose inputs and tools remain available. The Rust matrix separates Clippy,
  deterministic light-package shards, and heavy-profile tests at job level.
  Packages with very large explicit binary inventories use deterministic target
  shards plus one library/integration-test shard.
  General correctness shards use Cargo's `test` profile; optimized scientific
  audits retain their validation or parity profiles.

## sccache

- Hosted Rust matrix jobs use sccache 0.15.0 with a bounded local compiler
  cache. Every shard restores the same content-addressed archive. The first
  selected test shard publishes one updated archive after successful validation;
  the archive retains that shard's compiled dependency subset for later runs.
  One archive operation replaces per-compile GitHub cache writes, which hit
  the service rate limit when shards ran concurrently. Per-shard target archives
  remain prohibited because duplicated dependencies evict useful caches.
  Each shard retains JSON statistics and allowlisted write-error counts in its
  validation report; raw errors stay on the runner because response metadata
  can contain signed URLs. The setup action also reports cache statistics.
  Rust binary compilation and linking remain uncached. Every validation command
  runs on cache hits. Measure reuse from the reported hits before claiming a speedup.

## Hosted validation chain

| # | Check                    | Purpose                                                                          |
| - | ------------------------ | -------------------------------------------------------------------------------- |
| 1 | cache-check              | Soft cap (150G) + hard cap (250G) on `.cache/`                                   |
| 2 | terminology-gate         | 8 banned legacy terms; prefer `sign_imbalance` for the renamed crate vocabulary. |
| 3 | ansi-check               | Reject emojis and non-whitespace control characters; non-ASCII text passes       |
| 4 | validate-ci-scoped-rust  | Scoped clippy + nextest on changed-crate closure                                 |
| 5 | validate-governance      | Verify registry policy, signatures, cross-references, and checked-in TOMLs      |

The repository carries no hook installer, tracked pre-push executable, or
local compatibility gate target.

One CI workflow admits pull requests and main pushes, with superseded runs
canceled per event and ref. It routes benchmark, proof, paper, and unsafe-survey
jobs through reusable workflows, tests affected consumers, and lints directly
changed owners. Weekly full runs and explicit full dispatch cover the whole workspace.
Pull-request documentation checks render the registry-backed mdBook with a
two-minute job budget. A separate workflow publishes the full default-feature
Rust API and book site after successful main CI; Pages deployment requires
that publication to pass. A green pull-request book check does not prove full
Rust API documentation freshness. Set `DOCS_FEATURE_FLAGS=--all-features` only
on a host with the required SDKs.

## Validation and audit lanes

| Target                     | What it checks                                             |
| -------------------------- | ---------------------------------------------------------- |
| `make rust-clippy`         | Workspace clippy with deny warnings                        |
| `make rust-semver-check`   | semver-checks for crate API stability                       |
| `make cargo-deny-check`    | License, advisory, and source policy                        |
| `make dep-audit`           | cargo-audit advisory scan                                   |
| `make cpd-audit CPD_TOP=20`| PMD-driven duplication audit                                |
| `make docs-freshness`      | Generated docs match source registries                      |
| `make integrity`           | Verify lane (mirror + license + overflow)                   |
| `make registry-integrity`  | Regenerates `registry/schema_signatures.toml`               |

Any registry TOML edit drifts `schema_signatures.toml`; run
`make integrity-resolution` rather than patching signatures by hand.
