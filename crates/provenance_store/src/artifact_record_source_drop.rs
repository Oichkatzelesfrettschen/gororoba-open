//! Transactional removal of named `record_sources` references from artifacts.

use crate::{
    ProvenanceStore,
    artifact_paths::{mark_dry_run_replay, sha256},
};
use anyhow::{Context, Result, bail};
use chrono::Utc;
use rusqlite::{Connection, params};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeSet;

const ACTION: &str = "drop-artifact-record-sources";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactRecordSourceDropSpec {
    pub schema_version: u32,
    pub drop_key: String,
    pub actor: String,
    pub reason: String,
    pub drop: Vec<ArtifactRecordSourceDrop>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactRecordSourceDrop {
    pub id: String,
    /// Exact set of source references the artifact must hold now.
    pub expected_source_refs: Vec<String>,
    /// Subset that leaves the artifact's record sources.
    pub drop_refs: Vec<String>,
}

/// Source references of one artifact in the order the exports read them.
fn source_refs(connection: &Connection, id: &str) -> Result<Vec<String>> {
    let mut statement = connection.prepare(
        "SELECT source_ref FROM record_sources \
         WHERE entity_kind = 'artifact' AND entity_id = ?1 ORDER BY source_ref",
    )?;
    Ok(statement
        .query_map([id], |row| row.get::<_, String>(0))?
        .collect::<std::result::Result<_, _>>()?)
}

fn evidence_row(connection: &Connection, id: &str) -> Result<Value> {
    Ok(json!({"id": id, "source_refs": source_refs(connection, id)?}))
}

impl ProvenanceStore {
    /// Delete the named `record_sources` rows of each artifact and retain the before and after
    /// reference lists. `dry_run` runs every step and rolls the transaction back.
    pub fn drop_artifact_record_sources(
        &mut self,
        spec: &ArtifactRecordSourceDropSpec,
        dry_run: bool,
    ) -> Result<Value> {
        if spec.schema_version != 1 || spec.drop.is_empty() {
            bail!("record-source drop requires schema_version 1 and a nonempty drop set");
        }
        for (name, value) in [
            ("drop_key", &spec.drop_key),
            ("actor", &spec.actor),
            ("reason", &spec.reason),
        ] {
            if value.trim().is_empty() {
                bail!("{name} must be nonempty");
            }
        }
        let mut ids = BTreeSet::new();
        for entry in &spec.drop {
            if entry.id.is_empty() || !ids.insert(&entry.id) {
                bail!("empty or duplicate artifact ID {}", entry.id);
            }
            let expected: BTreeSet<_> = entry.expected_source_refs.iter().collect();
            let dropped: BTreeSet<_> = entry.drop_refs.iter().collect();
            if expected.len() != entry.expected_source_refs.len()
                || dropped.len() != entry.drop_refs.len()
                || dropped.is_empty()
                || !dropped.is_subset(&expected)
            {
                bail!(
                    "dropped references must be a distinct, nonempty subset of the expected set for {}",
                    entry.id
                );
            }
        }
        let spec_sha256 = sha256(serde_json::to_vec(spec)?);
        let transaction = self
            .conn
            .transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
        {
            let mut statement = transaction
                .prepare("SELECT details_json FROM export_runs WHERE action = ?1 ORDER BY id")?;
            let reports = statement.query_map([ACTION], |row| row.get::<_, String>(0))?;
            for report in reports {
                let mut report: Value = serde_json::from_str(&report?)?;
                if report["drop_key"] != spec.drop_key {
                    continue;
                }
                if report["spec_sha256"] != spec_sha256 {
                    bail!("drop key already records a different specification");
                }
                let retained = report["drops"]
                    .as_array()
                    .context("drop report lacks row evidence")?;
                if retained.len() != spec.drop.len() {
                    bail!("drop report row count mismatch");
                }
                for (entry, evidence) in spec.drop.iter().zip(retained) {
                    if evidence["id"] != entry.id
                        || evidence_row(&transaction, &entry.id)? != evidence["after"]
                    {
                        bail!("post-drop state drift for {}", entry.id);
                    }
                }
                mark_dry_run_replay(&mut report, dry_run);
                return Ok(report);
            }
        }
        let mut evidence = Vec::new();
        let mut delta = Vec::new();
        for entry in &spec.drop {
            let exists: i64 = transaction.query_row(
                "SELECT count(*) FROM artifacts WHERE id = ?1",
                [&entry.id],
                |row| row.get(0),
            )?;
            if exists != 1 {
                bail!("missing artifact {}", entry.id);
            }
            let before = evidence_row(&transaction, &entry.id)?;
            let held: BTreeSet<String> =
                source_refs(&transaction, &entry.id)?.into_iter().collect();
            let expected: BTreeSet<String> = entry.expected_source_refs.iter().cloned().collect();
            if held != expected {
                bail!("stale expected source reference set for {}", entry.id);
            }
            for reference in &entry.drop_refs {
                transaction.execute(
                    "DELETE FROM record_sources \
                     WHERE entity_kind = 'artifact' AND entity_id = ?1 AND source_ref = ?2",
                    params![entry.id, reference],
                )?;
                delta.push(format!("{}: drop record source {reference}", entry.id));
            }
            let after = evidence_row(&transaction, &entry.id)?;
            evidence.push(json!({"id": entry.id, "before": before, "after": after}));
        }
        let mut report = json!({"schema_version": 1, "drop_key": spec.drop_key, "actor": spec.actor,
            "reason": spec.reason, "spec_sha256": spec_sha256,
            "spec_hash_encoding": "serde_json serialization of typed specification",
            "spec": spec, "drops": evidence, "delta": delta});
        if dry_run {
            report["dry_run"] = Value::Bool(true);
            transaction.rollback()?;
            return Ok(report);
        }
        transaction.execute(
            "INSERT INTO export_runs (action, created_at, artifact_count, document_count, details_json) \
             VALUES (?1, ?2, ?3, 0, ?4)",
            params![
                ACTION,
                Utc::now().to_rfc3339(),
                spec.drop.len() as i64,
                serde_json::to_string(&report)?
            ],
        )?;
        transaction.commit()?;
        Ok(report)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    static NEXT: AtomicUsize = AtomicUsize::new(0);

    struct Fixture {
        directory: PathBuf,
        store: ProvenanceStore,
        spec: ArtifactRecordSourceDropSpec,
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.directory).expect("remove test fixture");
        }
    }

    const REFS: [&str; 2] = ["registry/gone.toml::document/3::RPT-1", "primary-source"];

    fn fixture() -> Fixture {
        let directory = std::env::temp_dir().join(format!(
            "record-source-drop-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let store = ProvenanceStore::open(&directory.join("test.sqlite3")).unwrap();
        for id in ["A", "B"] {
            store
                .conn
                .execute(
                    "INSERT INTO artifacts VALUES (?1, ?1, 'title', 'citation', 'citation_only_no_link', 0, NULL, NULL)",
                    [id],
                )
                .unwrap();
            for reference in REFS {
                store
                    .conn
                    .execute(
                        "INSERT INTO record_sources VALUES ('artifact', ?1, ?2)",
                        params![id, reference],
                    )
                    .unwrap();
            }
        }
        store
            .conn
            .execute(
                "INSERT INTO record_sources VALUES ('document', 'A', 'registry/gone.toml::document/3::RPT-1')",
                [],
            )
            .unwrap();
        let spec = ArtifactRecordSourceDropSpec {
            schema_version: 1,
            drop_key: "drop-test".into(),
            actor: "test".into(),
            reason: "the referenced record was removed".into(),
            drop: vec![ArtifactRecordSourceDrop {
                id: "A".into(),
                expected_source_refs: REFS.iter().map(|value| (*value).into()).collect(),
                drop_refs: vec![REFS[0].into()],
            }],
        };
        Fixture {
            directory,
            store,
            spec,
        }
    }

    fn export_run_count(fixture: &Fixture) -> i64 {
        fixture
            .store
            .conn
            .query_row("SELECT count(*) FROM export_runs", [], |row| row.get(0))
            .unwrap()
    }

    fn all_rows(fixture: &Fixture) -> Vec<(String, String, String)> {
        let mut statement = fixture
            .store
            .conn
            .prepare("SELECT * FROM record_sources ORDER BY 1, 2, 3")
            .unwrap();
        statement
            .query_map([], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)))
            .unwrap()
            .collect::<std::result::Result<_, _>>()
            .unwrap()
    }

    #[test]
    fn drop_removes_only_the_named_reference_and_replays_exactly() {
        let mut fixture = fixture();
        let report = fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, false)
            .unwrap();
        assert_eq!(source_refs(&fixture.store.conn, "A").unwrap(), [REFS[1]]);
        assert_eq!(
            source_refs(&fixture.store.conn, "B").unwrap(),
            ["primary-source", REFS[0]]
        );
        let documents: i64 = fixture
            .store
            .conn
            .query_row(
                "SELECT count(*) FROM record_sources WHERE entity_kind = 'document'",
                [],
                |row| row.get(0),
            )
            .unwrap();
        assert_eq!(documents, 1);
        assert_eq!(
            fixture
                .store
                .drop_artifact_record_sources(&fixture.spec, false)
                .unwrap(),
            report
        );
        assert_eq!(export_run_count(&fixture), 1);
        fixture.spec.reason.push_str(" changed");
        assert!(
            fixture
                .store
                .drop_artifact_record_sources(&fixture.spec, false)
                .is_err()
        );
        fixture.spec.reason = "the referenced record was removed".into();
        fixture
            .store
            .conn
            .execute(
                "INSERT INTO record_sources VALUES ('artifact', 'A', 'drift')",
                [],
            )
            .unwrap();
        assert!(
            fixture
                .store
                .drop_artifact_record_sources(&fixture.spec, false)
                .is_err()
        );
    }

    #[test]
    fn dry_run_reports_the_delta_and_leaves_the_store_unchanged() {
        let mut fixture = fixture();
        let before = all_rows(&fixture);
        let report = fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, true)
            .unwrap();
        assert_eq!(report["dry_run"], true);
        assert_eq!(report["delta"].as_array().unwrap().len(), 1);
        assert_eq!(all_rows(&fixture), before);
        assert_eq!(export_run_count(&fixture), 0);
        let applied = fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, false)
            .unwrap();
        assert_eq!(applied["delta"], report["delta"]);
    }

    #[test]
    fn the_whole_set_may_be_dropped() {
        let mut fixture = fixture();
        fixture.spec.drop[0].drop_refs = REFS.iter().map(|value| (*value).into()).collect();
        fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, false)
            .unwrap();
        assert!(source_refs(&fixture.store.conn, "A").unwrap().is_empty());
    }

    #[test]
    fn drop_rejects_invalid_admission_atomically() {
        for case in 0..8 {
            let mut fixture = fixture();
            let before = all_rows(&fixture);
            match case {
                0 => fixture.spec.drop[0].expected_source_refs.pop(),
                1 => {
                    fixture.spec.drop[0].drop_refs = vec!["absent".into()];
                    None
                }
                2 => {
                    fixture.spec.drop[0].drop_refs.clear();
                    None
                }
                3 => {
                    fixture.spec.drop.push(fixture.spec.drop[0].clone());
                    None
                }
                4 => {
                    fixture.spec.drop[0].id = "missing".into();
                    None
                }
                5 => {
                    fixture.spec.actor = " ".into();
                    None
                }
                6 => {
                    fixture.spec.drop[0].drop_refs.push(REFS[0].into());
                    None
                }
                7 => {
                    fixture.spec.schema_version = 2;
                    None
                }
                _ => unreachable!(),
            };
            assert!(
                fixture
                    .store
                    .drop_artifact_record_sources(&fixture.spec, false)
                    .is_err(),
                "case {case}"
            );
            assert_eq!(all_rows(&fixture), before, "case {case}");
            assert_eq!(export_run_count(&fixture), 0);
        }
    }

    #[test]
    fn drop_rolls_back_late_trigger_failure() {
        let mut fixture = fixture();
        let before = all_rows(&fixture);
        let mut second = fixture.spec.drop[0].clone();
        second.id = "B".into();
        fixture.spec.drop.push(second);
        fixture
            .store
            .conn
            .execute_batch(
                "CREATE TRIGGER reject_second BEFORE DELETE ON record_sources \
                 WHEN OLD.entity_id = 'B' BEGIN SELECT RAISE(ABORT, 'injected late failure'); END;",
            )
            .unwrap();
        assert!(
            fixture
                .store
                .drop_artifact_record_sources(&fixture.spec, false)
                .is_err()
        );
        assert_eq!(all_rows(&fixture), before);
        assert_eq!(export_run_count(&fixture), 0);
    }

    #[test]
    fn a_dry_run_against_an_applied_key_reports_the_replayed_content() {
        let mut fixture = fixture();
        let applied = fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, false)
            .unwrap();
        let rehearsal = fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, true)
            .unwrap();
        assert_eq!(rehearsal["dry_run"], true);
        assert_eq!(rehearsal["already_applied"], true);
        assert_eq!(rehearsal["delta"], applied["delta"]);
        assert_eq!(rehearsal["drops"], applied["drops"]);
        assert_eq!(export_run_count(&fixture), 1);
    }

    #[test]
    fn replay_compares_the_evidence_row_count_to_the_specification() {
        let mut fixture = fixture();
        fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, false)
            .unwrap();
        fixture
            .store
            .conn
            .execute(
                "UPDATE export_runs SET details_json = json_set(details_json, '$.drops', json('[]')) \
                 WHERE action = ?1",
                [ACTION],
            )
            .unwrap();
        let error = fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, false)
            .unwrap_err();
        assert!(
            error.to_string().contains("row count mismatch"),
            "{error:#}"
        );
    }

    #[test]
    fn replay_compares_the_evidence_ids_to_the_specification() {
        let mut fixture = fixture();
        fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, false)
            .unwrap();
        fixture
            .store
            .conn
            .execute(
                "UPDATE export_runs SET details_json = json_set(details_json, '$.drops[0].id', 'B') \
                 WHERE action = ?1",
                [ACTION],
            )
            .unwrap();
        let error = fixture
            .store
            .drop_artifact_record_sources(&fixture.spec, false)
            .unwrap_err();
        assert!(error.to_string().contains("state drift for A"), "{error:#}");
    }
}
