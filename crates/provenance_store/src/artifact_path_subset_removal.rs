//! Transactional removal of named download paths from an artifact that keeps other download
//! paths, its status and its canonical download path.

use crate::{
    ProvenanceStore,
    artifact_path_retirement::{check_relative, reject_tracked},
    artifact_paths::{sha256, snapshot},
};
use anyhow::{Context, Result, bail};
use chrono::Utc;
use rusqlite::{Connection, params};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{collections::BTreeSet, path::Path};

const ACTION: &str = "remove-artifact-download-paths";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactPathSubsetRemovalSpec {
    pub schema_version: u32,
    pub removal_key: String,
    pub actor: String,
    pub reason: String,
    pub remove: Vec<ArtifactPathSubsetRemoval>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactPathSubsetRemoval {
    pub id: String,
    /// Canonical download path the artifact must hold now, when it holds one. It stays.
    #[serde(default)]
    pub expected_canonical_path: Option<String>,
    /// Exact set of `downloaded` paths the artifact must hold now.
    pub expected_downloaded_paths: Vec<String>,
    /// Untracked subset that leaves the `downloaded` relation for `historical_download`.
    pub remove_paths: Vec<String>,
}

fn replay(
    transaction: &Connection,
    spec: &ArtifactPathSubsetRemovalSpec,
    spec_sha256: &str,
) -> Result<Option<Value>> {
    let mut statement = transaction
        .prepare("SELECT details_json FROM export_runs WHERE action = ?1 ORDER BY id")?;
    let reports = statement.query_map([ACTION], |row| row.get::<_, String>(0))?;
    for report in reports {
        let report: Value = serde_json::from_str(&report?)?;
        if report["removal_key"] != spec.removal_key {
            continue;
        }
        if report["spec_sha256"] != spec_sha256 {
            bail!("removal key already records a different specification");
        }
        let retained = report["removals"]
            .as_array()
            .context("removal report lacks row evidence")?;
        if retained.len() != spec.remove.len() {
            bail!("removal report row count mismatch");
        }
        for (removal, evidence) in spec.remove.iter().zip(retained) {
            if evidence["id"] != removal.id
                || snapshot(transaction, &removal.id)? != evidence["after"]
            {
                bail!("post-removal state drift for {}", removal.id);
            }
        }
        return Ok(Some(report));
    }
    Ok(None)
}

impl ProvenanceStore {
    /// Move `remove_paths` from `downloaded` to `historical_download` for each named artifact,
    /// leaving the other downloaded paths, the status and the canonical path as they are.
    /// `dry_run` runs every step and rolls the transaction back.
    pub fn remove_artifact_download_paths(
        &mut self,
        repo_root: &Path,
        spec: &ArtifactPathSubsetRemovalSpec,
        dry_run: bool,
    ) -> Result<Value> {
        if spec.schema_version != 1 || spec.remove.is_empty() {
            bail!("removal requires schema_version 1 and a nonempty remove set");
        }
        for (name, value) in [
            ("removal_key", &spec.removal_key),
            ("actor", &spec.actor),
            ("reason", &spec.reason),
        ] {
            if value.trim().is_empty() {
                bail!("{name} must be nonempty");
            }
        }
        let mut ids = BTreeSet::new();
        for removal in &spec.remove {
            if removal.id.is_empty() || !ids.insert(&removal.id) {
                bail!("empty or duplicate artifact ID {}", removal.id);
            }
            let expected: BTreeSet<_> = removal.expected_downloaded_paths.iter().collect();
            let removed: BTreeSet<_> = removal.remove_paths.iter().collect();
            if expected.is_empty() || expected.len() != removal.expected_downloaded_paths.len() {
                bail!(
                    "expected downloaded paths must be distinct and nonempty for {}",
                    removal.id
                );
            }
            if removed.is_empty() || removed.len() != removal.remove_paths.len() {
                bail!(
                    "removed paths must be distinct and nonempty for {}",
                    removal.id
                );
            }
            if !removed.is_subset(&expected) || removed.len() == expected.len() {
                bail!(
                    "removed paths must be a proper subset of the downloaded set for {}; \
                     retire-paths handles removal of the whole set",
                    removal.id
                );
            }
            if let Some(canonical) = &removal.expected_canonical_path {
                if !expected.contains(canonical) {
                    bail!(
                        "expected canonical path must belong to the downloaded set for {}",
                        removal.id
                    );
                }
                if removed.contains(canonical) {
                    bail!(
                        "the canonical download path cannot leave the downloaded set for {}",
                        removal.id
                    );
                }
            }
            for path in expected {
                check_relative(path)?;
            }
            for path in removed {
                reject_tracked(repo_root, path)?;
            }
        }
        let spec_sha256 = sha256(serde_json::to_vec(spec)?);
        let transaction = self
            .conn
            .transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
        if let Some(report) = replay(&transaction, spec, &spec_sha256)? {
            return Ok(report);
        }
        let mut evidence = Vec::new();
        let mut delta = Vec::new();
        for removal in &spec.remove {
            let before = snapshot(&transaction, &removal.id)?;
            let artifacts = before["artifact"]
                .as_array()
                .context("artifact snapshot is not an array")?;
            if artifacts.len() != 1 {
                bail!("missing artifact {}", removal.id);
            }
            let canonical = artifacts[0]["canonical_download_path"]
                .as_str()
                .filter(|path| !path.is_empty());
            if canonical != removal.expected_canonical_path.as_deref() {
                bail!("stale expected canonical path for {}", removal.id);
            }
            let downloaded: BTreeSet<&str> = before["artifact_paths"]
                .as_array()
                .context("path snapshot is not an array")?
                .iter()
                .filter(|row| row["relation"] == "downloaded")
                .filter_map(|row| row["path"].as_str())
                .collect();
            let expected: BTreeSet<&str> = removal
                .expected_downloaded_paths
                .iter()
                .map(String::as_str)
                .collect();
            if downloaded != expected {
                bail!("stale expected downloaded path set for {}", removal.id);
            }
            for path in &removal.remove_paths {
                transaction.execute(
                    "INSERT INTO artifact_paths (artifact_id, path, relation) \
                     VALUES (?1, ?2, 'historical_download') ON CONFLICT DO NOTHING",
                    params![removal.id, path],
                )?;
                transaction.execute(
                    "DELETE FROM artifact_paths \
                     WHERE artifact_id = ?1 AND path = ?2 AND relation = 'downloaded'",
                    params![removal.id, path],
                )?;
            }
            let after = snapshot(&transaction, &removal.id)?;
            delta.push(format!(
                "{}: {} downloaded path(s) -> {} kept, {} moved to historical_download; status {} and canonical path unchanged",
                removal.id,
                removal.expected_downloaded_paths.len(),
                removal.expected_downloaded_paths.len() - removal.remove_paths.len(),
                removal.remove_paths.len(),
                artifacts[0]["status"].as_str().unwrap_or_default()
            ));
            evidence.push(json!({"id": removal.id, "before": before, "after": after}));
        }
        let mut report = json!({"schema_version": 1, "removal_key": spec.removal_key, "actor": spec.actor,
            "reason": spec.reason, "spec_sha256": spec_sha256,
            "spec_hash_encoding": "serde_json serialization of typed specification",
            "spec": spec, "removals": evidence, "delta": delta});
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
                spec.remove.len() as i64,
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
    use crate::artifact_paths::repository_git;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    static NEXT: AtomicUsize = AtomicUsize::new(0);

    struct Fixture {
        root: PathBuf,
        store: ProvenanceStore,
        spec: ArtifactPathSubsetRemovalSpec,
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.root).expect("remove test fixture");
        }
    }

    fn git(root: &Path, arguments: &[&str]) {
        let output = repository_git(root).args(arguments).output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    const DOWNLOADED: [&str; 4] = [
        "kept/tracked.toml",
        "kept/untracked.csv",
        "gone/a.pdf",
        "gone/dir/",
    ];

    fn fixture() -> Fixture {
        let root = std::env::temp_dir().join(format!(
            "artifact-subset-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(root.join("kept")).unwrap();
        fs::write(root.join("kept/tracked.toml"), b"tracked bytes").unwrap();
        git(&root, &["init", "--quiet"]);
        git(&root, &["add", "--", "kept/tracked.toml"]);
        let store = ProvenanceStore::open(&root.join("test.sqlite3")).unwrap();
        for id in ["A", "B"] {
            store
                .conn
                .execute(
                    "INSERT INTO artifacts VALUES (?1, ?1, 'title', 'citation', 'downloaded', 1, 'https://example.org', 'kept/tracked.toml')",
                    [id],
                )
                .unwrap();
            for path in DOWNLOADED {
                store
                    .conn
                    .execute(
                        "INSERT INTO artifact_paths VALUES (?1, ?2, 'downloaded')",
                        params![id, path],
                    )
                    .unwrap();
            }
            store
                .conn
                .execute(
                    "INSERT INTO artifact_paths VALUES (?1, 'source.txt', 'referenced')",
                    [id],
                )
                .unwrap();
            store
                .conn
                .execute(
                    "INSERT INTO lane_assignments VALUES (?1, 'papers_pdf')",
                    [id],
                )
                .unwrap();
        }
        let spec = ArtifactPathSubsetRemovalSpec {
            schema_version: 1,
            removal_key: "removal-test".into(),
            actor: "test".into(),
            reason: "the removed paths left the tree".into(),
            remove: vec![ArtifactPathSubsetRemoval {
                id: "A".into(),
                expected_canonical_path: Some("kept/tracked.toml".into()),
                expected_downloaded_paths: DOWNLOADED.iter().map(|path| (*path).into()).collect(),
                remove_paths: vec!["gone/a.pdf".into(), "gone/dir/".into()],
            }],
        };
        Fixture { root, store, spec }
    }

    fn export_run_count(fixture: &Fixture) -> i64 {
        fixture
            .store
            .conn
            .query_row("SELECT count(*) FROM export_runs", [], |row| row.get(0))
            .unwrap()
    }

    fn apply(fixture: &mut Fixture, dry_run: bool) -> Result<Value> {
        fixture
            .store
            .remove_artifact_download_paths(&fixture.root, &fixture.spec, dry_run)
    }

    #[test]
    fn removal_moves_only_the_named_paths_and_replays_exactly() {
        let mut fixture = fixture();
        let untouched = snapshot(&fixture.store.conn, "B").unwrap();
        let report = apply(&mut fixture, false).unwrap();
        let after = &report["removals"][0]["after"];
        assert_eq!(after["artifact"][0]["status"], "downloaded");
        assert_eq!(
            after["artifact"][0]["canonical_download_path"],
            "kept/tracked.toml"
        );
        let relation_of = |path: &str| -> Vec<String> {
            after["artifact_paths"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|row| row["path"] == path)
                .map(|row| row["relation"].as_str().unwrap().to_string())
                .collect()
        };
        assert_eq!(relation_of("kept/tracked.toml"), ["downloaded"]);
        assert_eq!(relation_of("kept/untracked.csv"), ["downloaded"]);
        assert_eq!(relation_of("gone/a.pdf"), ["historical_download"]);
        assert_eq!(relation_of("gone/dir/"), ["historical_download"]);
        assert_eq!(relation_of("source.txt"), ["referenced"]);
        assert_eq!(snapshot(&fixture.store.conn, "B").unwrap(), untouched);
        assert_eq!(apply(&mut fixture, false).unwrap(), report);
        assert_eq!(export_run_count(&fixture), 1);
        fixture.spec.reason.push_str(" changed");
        assert!(apply(&mut fixture, false).is_err());
        fixture.spec.reason = "the removed paths left the tree".into();
        fixture
            .store
            .conn
            .execute("UPDATE artifacts SET title = 'drift' WHERE id = 'A'", [])
            .unwrap();
        assert!(apply(&mut fixture, false).is_err());
    }

    #[test]
    fn dry_run_reports_the_delta_and_leaves_the_store_unchanged() {
        let mut fixture = fixture();
        let before = snapshot(&fixture.store.conn, "A").unwrap();
        let report = apply(&mut fixture, true).unwrap();
        assert_eq!(report["dry_run"], true);
        assert_eq!(report["delta"].as_array().unwrap().len(), 1);
        assert_eq!(snapshot(&fixture.store.conn, "A").unwrap(), before);
        assert_eq!(export_run_count(&fixture), 0);
        let applied = apply(&mut fixture, false).unwrap();
        assert_eq!(applied["delta"], report["delta"]);
    }

    #[test]
    fn removal_rejects_invalid_admission_atomically() {
        for case in 0..11 {
            let mut fixture = fixture();
            let before = snapshot(&fixture.store.conn, "A").unwrap();
            match case {
                0 => fixture.spec.remove[0].expected_canonical_path = Some("wrong".into()),
                1 => fixture.spec.remove[0]
                    .expected_downloaded_paths
                    .push("extra".into()),
                2 => fixture.spec.remove[0].remove_paths = vec!["gone/missing.pdf".into()],
                3 => {
                    fixture.spec.remove[0].remove_paths =
                        DOWNLOADED.iter().map(|path| (*path).into()).collect()
                }
                4 => fixture.spec.remove[0].remove_paths = vec!["kept/tracked.toml".into()],
                5 => fixture.spec.remove[0].remove_paths = vec!["../escape".into()],
                6 => fixture.spec.remove.push(fixture.spec.remove[0].clone()),
                7 => fixture.spec.remove[0].id = "missing".into(),
                8 => fixture.spec.actor = " ".into(),
                9 => fixture.spec.remove[0].remove_paths = Vec::new(),
                10 => {
                    fixture.spec.remove[0].remove_paths =
                        vec!["gone/a.pdf".into(), "gone/a.pdf".into()]
                }
                _ => unreachable!(),
            }
            assert!(apply(&mut fixture, false).is_err(), "case {case}");
            assert_eq!(snapshot(&fixture.store.conn, "A").unwrap(), before);
            assert_eq!(export_run_count(&fixture), 0);
        }
    }

    #[test]
    fn removal_rejects_tracked_paths_and_missing_repository() {
        let mut fixture = fixture();
        fs::create_dir_all(fixture.root.join("gone")).unwrap();
        fs::write(fixture.root.join("gone/a.pdf"), b"tracked").unwrap();
        git(&fixture.root, &["add", "--", "gone/a.pdf"]);
        let error = apply(&mut fixture, false).unwrap_err();
        assert!(error.to_string().contains("Git-tracked"), "{error:#}");
        git(
            &fixture.root,
            &["rm", "--cached", "--quiet", "--", "gone/a.pdf"],
        );
        fs::rename(fixture.root.join(".git"), fixture.root.join("retained-git")).unwrap();
        let error = apply(&mut fixture, false).unwrap_err();
        assert!(
            error.to_string().contains("Git index lookup failed"),
            "{error:#}"
        );
    }

    #[test]
    fn a_directory_pathspec_rejects_when_any_tracked_file_remains_under_it() {
        let mut fixture = fixture();
        fs::create_dir_all(fixture.root.join("gone/dir")).unwrap();
        fs::write(fixture.root.join("gone/dir/inner.txt"), b"tracked").unwrap();
        git(&fixture.root, &["add", "--", "gone/dir/inner.txt"]);
        assert!(apply(&mut fixture, false).is_err());
    }

    #[test]
    fn removal_rolls_back_late_trigger_failure() {
        let mut fixture = fixture();
        let before = snapshot(&fixture.store.conn, "A").unwrap();
        let mut second = fixture.spec.remove[0].clone();
        second.id = "B".into();
        fixture.spec.remove.push(second);
        fixture
            .store
            .conn
            .execute_batch(
                "CREATE TRIGGER reject_second BEFORE DELETE ON artifact_paths \
                 WHEN OLD.artifact_id = 'B' BEGIN SELECT RAISE(ABORT, 'injected late failure'); END;",
            )
            .unwrap();
        assert!(apply(&mut fixture, false).is_err());
        assert_eq!(snapshot(&fixture.store.conn, "A").unwrap(), before);
        assert_eq!(export_run_count(&fixture), 0);
    }

    #[test]
    fn mutated_store_keeps_the_canonical_path_invariant() {
        let mut fixture = fixture();
        fixture
            .store
            .conn
            .execute(
                "UPDATE artifacts SET canonical_download_path = NULL WHERE id = 'B'",
                [],
            )
            .unwrap();
        fixture.store.verify_invariants(&fixture.root).unwrap();
        apply(&mut fixture, false).unwrap();
        fixture.store.verify_invariants(&fixture.root).unwrap();
    }
}
