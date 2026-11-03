SPDX-License-Identifier: GPL-2.0-or-later

POLITICAL OBSERVATORY - FIRST EMPIRICAL PACKAGE
2026-11-03

Status: first source-discovery pass and curated primary-summary pilot.
This is not an exhaustive acquisition, a fitted model, a November local opinion
estimate, a result prediction, or evidence of political quantum/32D advantage.

Contents:
 sources.json       62 inspected source surfaces across 24 domain categories.
 pilot.json         131 observations in 20 studies/reporting periods.
 pilot_audit.json   Independent SQLite checks and seven descriptive contrasts.
 schema.sql         Separate strict SQLite observation-ledger schema.
 PROTOCOL.txt       Targets, geography, timestamps, source controls, model
                    architecture, validation gates and falsifiers.
 literature.json    13 existing works/repository references and implementation
                    crosswalk; Spanish catalog notes, not validated item translations.
 coverage.json      Missing domains, access limits, quarantines and expansion queue.

Rust entrypoint (Python is not an implementation dependency):
 cargo run -p gororoba_cli_data --example political_observatory -- \
   --bundle docs/research/political_observatory \
   --cutoff 2026-11-03T18:59:14.557Z \
   --report /absolute/path/to/new-political-audit.json

Focused developer diagnostics:
 cargo check -p gororoba_cli_data --example political_observatory
 cargo test -p gororoba_cli_data --example political_observatory

The report path must not exist. Bundle path is caller-supplied; no repository
location is compiled into the executable. The Rust example uses existing crate
dependencies and does not fetch providers, infer uncertainty from rounded
percentages, fit a model or submit QPU jobs. It has 11 authored tests.

Validation:
 - All 131 observations inserted successfully into the strict SQLite schema.
 - Integrity, foreign keys, cutoff admission and invalid-record rejection checks
   passed in an independent standard-library SQLite cross-check.
 - Seven differences agreed with separately specified expected arithmetic.
 - Rust toolchain is unavailable in this execution environment. Rust code and
   its authored tests were not compiled or executed here.
 - GitHub Actions remains the repository-validation authority. A branch push
   does not by itself establish a passing result.

Important interpretation:
 - 131 is a record count, not an independent sample size.
 - Pasadena's 12 pilot records are YES/NO counts for six 2024 measures.
   They do not measure November 2026 city opinion or current city turnout.
 - LA County's five pilot records are March 2026 quality-of-life measures.
 - LA metro CPI covers LA and Orange counties and is a separate geography.
 - National/foreign sources supply context; national model fitting follows
   validation of the requested local/county/state layers.
 - A source catalog entry is not a bulk download or approved data license.
 - Historical reference dates do not establish original data vintages.
   This pilot deliberately uses retrieval as conservative first-known availability.
 - No litigation cohort, protest/strike outcome panel, travel series or social
   corpus was ingested in this pass. Their numeric models remain unavailable.

Next concrete acquisition:
Reconcile historical LA community/precinct returns and Pasadena boundaries;
acquire Pasadena taxable sales and recovery series; assess authorized LA panel
access; enumerate CA/TX/KS polling waves and historical economic vintages.
Use the provider/geography/domain/period denominator specified in PROTOCOL.txt
to assess completeness. Never announce an exhaustive model from this pilot.

