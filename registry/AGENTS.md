# Registry agent guide

Root `AGENTS.md` carries the prohibitions; this file carries the procedure.
`docs/engineering/registry_canonical_architecture.md` describes the four layers
(SQLite -> compatibility TOMLs -> Rust mirrors -> docs) and
`docs/engineering/repo_audit_metric_taxonomy.md` the audit metrics.

## Mutation workflow

1. Edit through `gororoba-db` (crate `crates/gororoba_db/`) against
   `registry/canonical/control_plane.sqlite3`.
2. Re-export: `cargo run -p gororoba_cli_provenance --bin provenance -- export-control-plane`.
3. Refresh signatures: `make registry-integrity`. A registry TOML edit drifts
   `registry/schema_signatures.toml`; run `make integrity-resolution` rather
   than patching signatures by hand.
4. Commit the SQLite delta, regenerated TOMLs and regenerated markdown in one
   commit.

`registry/source_manifest.toml` lists the lanes that round-trip; unmigrated
lanes it names stay hand-authored canonical inputs.

## Destructive import

`gororoba-db build` calls `build_fresh`, deletes the database file and reloads
only manifest lanes. Transition events, the relations they allocate and the
revision log have no lane, and removing the file issues no DELETE, so the
append-only triggers never fire. `crates/provenance_store/src/reimport_guard.rs`
refuses when history exists unless `--allow-transition-history-loss` is passed.

## Typed contracts

- `gororoba-db claim set-evidence --spec <contract.toml> --actor <actor> --reason <reason>`
- `gororoba-db artifact record-retrieval --spec <receipt.toml>`

Both append canonical history; follow steps 2-4 afterwards.
`ClaimEvidenceSpec` in `provenance_store::claim_evidence` defines the fields;
`depth_status = "not_assessed"` requires an omitted `lift_depth` and a rationale.
