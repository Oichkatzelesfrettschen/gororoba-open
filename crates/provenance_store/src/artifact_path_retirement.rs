//! Transactional retirement of artifact download paths that no tracked file replaces.

use crate::{
    ProvenanceStore,
    artifact_paths::{repository_git, sha256, snapshot},
};
use anyhow::{Context, Result, bail};
use chrono::Utc;
use rusqlite::params;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    collections::BTreeSet,
    path::{Component, Path},
};

const ACTION: &str = "retire-artifact-paths";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactPathRetirementSpec {
    pub schema_version: u32,
    pub retire_key: String,
    pub actor: String,
    pub reason: String,
    pub retire: Vec<ArtifactPathRetirement>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactPathRetirement {
    pub id: String,
    /// Canonical download path the artifact must hold now, when it holds one.
    #[serde(default)]
    pub expected_canonical_path: Option<String>,
    /// Exact set of `downloaded` paths the artifact must hold now.
    pub expected_downloaded_paths: Vec<String>,
    /// Status the artifact takes once no `downloaded` path remains.
    pub new_status: RetiredArtifactStatus,
}

/// The `artifacts.status` values that `ProvenanceStore::verify_invariants`
/// accepts and that claim no local download.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RetiredArtifactStatus {
    Downloadable,
    Blocked,
    CitationOnlyNoLink,
    Unverified,
}

impl RetiredArtifactStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::Downloadable => "downloadable",
            Self::Blocked => "blocked",
            Self::CitationOnlyNoLink => "citation_only_no_link",
            Self::Unverified => "unverified",
        }
    }
}

pub(crate) fn check_relative(path: &str) -> Result<()> {
    if path.is_empty()
        || !Path::new(path)
            .components()
            .all(|part| matches!(part, Component::Normal(_)))
    {
        bail!("artifact path must contain only repository-relative normal components: {path}");
    }
    Ok(())
}

/// A tracked file means a replacement exists and `repair_artifact_paths` is
/// the verb; retirement applies only where the index holds no entry.
pub(crate) fn reject_tracked(root: &Path, path: &str) -> Result<()> {
    let output = repository_git(root)
        .arg("--literal-pathspecs")
        .args(["ls-files", "-z", "--", path])
        .output()
        .context("inspect artifact Git index membership")?;
    if !output.status.success() {
        bail!(
            "artifact repository Git index lookup failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }
    if !output.stdout.is_empty() {
        bail!("artifact path is Git-tracked; repair it with a replacement instead: {path}");
    }
    Ok(())
}

impl ProvenanceStore {
    /// Move a bounded artifact set from `downloaded` to `historical_download`
    /// paths, set a non-download status, and retain row evidence atomically.
    pub fn retire_artifact_paths(
        &mut self,
        repo_root: &Path,
        spec: &ArtifactPathRetirementSpec,
    ) -> Result<Value> {
        if spec.schema_version != 1 || spec.retire.is_empty() {
            bail!("retirement requires schema_version 1 and a nonempty retire set");
        }
        for (name, value) in [
            ("retire_key", &spec.retire_key),
            ("actor", &spec.actor),
            ("reason", &spec.reason),
        ] {
            if value.trim().is_empty() {
                bail!("{name} must be nonempty");
            }
        }
        let mut ids = BTreeSet::new();
        for retirement in &spec.retire {
            if retirement.id.is_empty() || !ids.insert(&retirement.id) {
                bail!("empty or duplicate artifact ID {}", retirement.id);
            }
            let old: BTreeSet<_> = retirement.expected_downloaded_paths.iter().collect();
            if old.is_empty() || old.len() != retirement.expected_downloaded_paths.len() {
                bail!(
                    "expected downloaded paths must be distinct and nonempty for {}",
                    retirement.id
                );
            }
            for path in &old {
                check_relative(path)?;
                reject_tracked(repo_root, path)?;
            }
            if let Some(canonical) = &retirement.expected_canonical_path
                && !old.contains(canonical)
            {
                bail!(
                    "expected canonical path must belong to the downloaded set for {}",
                    retirement.id
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
                let report: Value = serde_json::from_str(&report?)?;
                if report["retire_key"] == spec.retire_key {
                    if report["spec_sha256"] != spec_sha256 {
                        bail!("retire key already records a different specification");
                    }
                    let retained = report["retirements"]
                        .as_array()
                        .context("retirement report lacks row evidence")?;
                    if retained.len() != spec.retire.len() {
                        bail!("retirement report row count mismatch");
                    }
                    for (retirement, evidence) in spec.retire.iter().zip(retained) {
                        if evidence["id"] != retirement.id
                            || snapshot(&transaction, &retirement.id)? != evidence["after"]
                        {
                            bail!("post-retirement state drift for {}", retirement.id);
                        }
                    }
                    return Ok(report);
                }
            }
        }
        let mut evidence = Vec::new();
        for retirement in &spec.retire {
            let before = snapshot(&transaction, &retirement.id)?;
            let artifacts = before["artifact"]
                .as_array()
                .context("artifact snapshot is not an array")?;
            if artifacts.len() != 1 {
                bail!("missing artifact {}", retirement.id);
            }
            let artifact = &artifacts[0];
            let canonical = artifact["canonical_download_path"]
                .as_str()
                .filter(|path| !path.is_empty());
            if canonical != retirement.expected_canonical_path.as_deref() {
                bail!("stale expected canonical path for {}", retirement.id);
            }
            if retirement.new_status == RetiredArtifactStatus::Downloadable
                && artifact["canonical_functional_url"]
                    .as_str()
                    .is_none_or(str::is_empty)
            {
                bail!(
                    "status downloadable requires a canonical functional URL for {}",
                    retirement.id
                );
            }
            let downloaded: BTreeSet<&str> = before["artifact_paths"]
                .as_array()
                .context("path snapshot is not an array")?
                .iter()
                .filter(|row| row["relation"] == "downloaded")
                .filter_map(|row| row["path"].as_str())
                .collect();
            let expected: BTreeSet<&str> = retirement
                .expected_downloaded_paths
                .iter()
                .map(String::as_str)
                .collect();
            if downloaded != expected {
                bail!("stale expected downloaded path set for {}", retirement.id);
            }
            for path in &retirement.expected_downloaded_paths {
                transaction.execute(
                    "INSERT INTO artifact_paths (artifact_id, path, relation) VALUES (?1, ?2, 'historical_download') ON CONFLICT DO NOTHING",
                    params![retirement.id, path],
                )?;
            }
            transaction.execute(
                "DELETE FROM artifact_paths WHERE artifact_id = ?1 AND relation = 'downloaded'",
                [&retirement.id],
            )?;
            transaction.execute(
                "UPDATE artifacts SET status = ?2, canonical_download_path = NULL WHERE id = ?1",
                params![retirement.id, retirement.new_status.as_str()],
            )?;
            let after = snapshot(&transaction, &retirement.id)?;
            evidence.push(json!({"id": retirement.id, "before": before, "after": after}));
        }
        let report = json!({"schema_version": 1, "retire_key": spec.retire_key, "actor": spec.actor, "reason": spec.reason,
            "spec_sha256": spec_sha256, "spec_hash_encoding": "serde_json serialization of typed specification", "spec": spec, "retirements": evidence});
        transaction.execute(
            "INSERT INTO export_runs (action, created_at, artifact_count, document_count, details_json) VALUES (?1, ?2, ?3, 0, ?4)",
            params![
                ACTION,
                Utc::now().to_rfc3339(),
                spec.retire.len() as i64,
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
        root: PathBuf,
        store: ProvenanceStore,
        spec: ArtifactPathRetirementSpec,
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

    fn fixture() -> Fixture {
        let root = std::env::temp_dir().join(format!(
            "artifact-retire-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        fs::write(root.join("kept.txt"), b"tracked bytes").unwrap();
        git(&root, &["init", "--quiet"]);
        git(&root, &["add", "--", "kept.txt"]);
        let store = ProvenanceStore::open(&root.join("test.sqlite3")).unwrap();
        for id in ["A", "B"] {
            store
                .conn
                .execute(
                    "INSERT INTO artifacts VALUES (?1, ?1, 'title', 'citation', 'downloaded', 1, 'https://example.org', 'gone/a.pdf')",
                    [id],
                )
                .unwrap();
            for (path, relation) in [
                ("gone/a.pdf", "downloaded"),
                ("gone/b.pdf", "downloaded"),
                ("source.txt", "referenced"),
            ] {
                store
                    .conn
                    .execute(
                        "INSERT INTO artifact_paths VALUES (?1, ?2, ?3)",
                        params![id, path, relation],
                    )
                    .unwrap();
            }
            store
                .conn
                .execute(
                    "INSERT INTO lane_assignments VALUES (?1, 'papers_pdf')",
                    [id],
                )
                .unwrap();
        }
        let spec = ArtifactPathRetirementSpec {
            schema_version: 1,
            retire_key: "retire-test".into(),
            actor: "test".into(),
            reason: "no copy can be materialized".into(),
            retire: vec![ArtifactPathRetirement {
                id: "A".into(),
                expected_canonical_path: Some("gone/a.pdf".into()),
                expected_downloaded_paths: vec!["gone/a.pdf".into(), "gone/b.pdf".into()],
                new_status: RetiredArtifactStatus::Downloadable,
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

    #[test]
    fn retirement_relabels_paths_status_and_replays_exactly() {
        let mut fixture = fixture();
        let untouched = snapshot(&fixture.store.conn, "B").unwrap();
        let report = fixture
            .store
            .retire_artifact_paths(&fixture.root, &fixture.spec)
            .unwrap();
        let after = &report["retirements"][0]["after"];
        assert_eq!(after["artifact"][0]["status"], "downloadable");
        assert!(after["artifact"][0]["canonical_download_path"].is_null());
        let paths = after["artifact_paths"].as_array().unwrap();
        assert!(paths.iter().all(|row| row["relation"] != "downloaded"));
        for path in ["gone/a.pdf", "gone/b.pdf"] {
            assert!(
                paths
                    .iter()
                    .any(|row| row["path"] == path && row["relation"] == "historical_download")
            );
        }
        assert!(
            paths
                .iter()
                .any(|row| row["path"] == "source.txt" && row["relation"] == "referenced")
        );
        let before = &report["retirements"][0]["before"]["artifact"][0];
        for (name, value) in before.as_object().unwrap() {
            if name != "status" && name != "canonical_download_path" {
                assert_eq!(value, &after["artifact"][0][name]);
            }
        }
        assert_eq!(snapshot(&fixture.store.conn, "B").unwrap(), untouched);
        assert_eq!(
            fixture
                .store
                .retire_artifact_paths(&fixture.root, &fixture.spec)
                .unwrap(),
            report
        );
        assert_eq!(export_run_count(&fixture), 1);
        fixture.spec.reason.push_str(" changed");
        assert!(
            fixture
                .store
                .retire_artifact_paths(&fixture.root, &fixture.spec)
                .is_err()
        );
        fixture.spec.reason = "no copy can be materialized".into();
        fixture
            .store
            .conn
            .execute("UPDATE artifacts SET title = 'drift' WHERE id = 'A'", [])
            .unwrap();
        assert!(
            fixture
                .store
                .retire_artifact_paths(&fixture.root, &fixture.spec)
                .is_err()
        );
    }

    #[test]
    fn retired_store_passes_download_path_invariant() {
        let mut fixture = fixture();
        assert!(fixture.store.verify_invariants(&fixture.root).is_err());
        fixture
            .store
            .conn
            .execute(
                "UPDATE artifacts SET canonical_download_path = NULL WHERE id = 'B'",
                [],
            )
            .unwrap();
        fixture
            .store
            .retire_artifact_paths(&fixture.root, &fixture.spec)
            .unwrap();
        fixture.store.verify_invariants(&fixture.root).unwrap();
    }

    #[test]
    fn retirement_rejects_invalid_admission_atomically() {
        for case in 0..9 {
            let mut fixture = fixture();
            let before = snapshot(&fixture.store.conn, "A").unwrap();
            match case {
                0 => fixture.spec.retire[0].expected_canonical_path = Some("wrong".into()),
                1 => fixture.spec.retire[0]
                    .expected_downloaded_paths
                    .push("extra".into()),
                2 => fixture.spec.retire[0].expected_downloaded_paths = vec!["../escape".into()],
                3 => fixture.spec.retire[0].expected_downloaded_paths = vec!["/absolute".into()],
                4 => fixture.spec.retire.push(fixture.spec.retire[0].clone()),
                5 => fixture.spec.retire[0].id = "missing".into(),
                6 => fixture.spec.retire[0].expected_canonical_path = None,
                7 => fixture.spec.actor = " ".into(),
                8 => {
                    fixture
                        .store
                        .conn
                        .execute(
                            "UPDATE artifacts SET canonical_functional_url = NULL WHERE id = 'A'",
                            [],
                        )
                        .unwrap();
                }
                _ => unreachable!(),
            }
            let before = if case == 8 {
                snapshot(&fixture.store.conn, "A").unwrap()
            } else {
                before
            };
            assert!(
                fixture
                    .store
                    .retire_artifact_paths(&fixture.root, &fixture.spec)
                    .is_err(),
                "case {case}"
            );
            assert_eq!(snapshot(&fixture.store.conn, "A").unwrap(), before);
            assert_eq!(export_run_count(&fixture), 0);
        }
    }

    #[test]
    fn retirement_without_a_functional_url_accepts_citation_only_status() {
        let mut fixture = fixture();
        fixture
            .store
            .conn
            .execute(
                "UPDATE artifacts SET canonical_functional_url = NULL WHERE id = 'A'",
                [],
            )
            .unwrap();
        fixture.spec.retire[0].new_status = RetiredArtifactStatus::CitationOnlyNoLink;
        let report = fixture
            .store
            .retire_artifact_paths(&fixture.root, &fixture.spec)
            .unwrap();
        assert_eq!(
            report["retirements"][0]["after"]["artifact"][0]["status"],
            "citation_only_no_link"
        );
    }

    #[test]
    fn retirement_rejects_tracked_paths() {
        let mut fixture = fixture();
        fs::create_dir(fixture.root.join("gone")).unwrap();
        fs::write(fixture.root.join("gone/a.pdf"), b"tracked").unwrap();
        git(&fixture.root, &["add", "--", "gone/a.pdf"]);
        let before = snapshot(&fixture.store.conn, "A").unwrap();
        let error = fixture
            .store
            .retire_artifact_paths(&fixture.root, &fixture.spec)
            .unwrap_err();
        assert!(error.to_string().contains("Git-tracked"), "{error:#}");
        assert_eq!(snapshot(&fixture.store.conn, "A").unwrap(), before);
    }

    #[test]
    fn retirement_rejects_missing_git_repository() {
        let mut fixture = fixture();
        fs::rename(fixture.root.join(".git"), fixture.root.join("retained-git")).unwrap();
        let error = fixture
            .store
            .retire_artifact_paths(&fixture.root, &fixture.spec)
            .unwrap_err();
        assert!(
            error.to_string().contains("Git index lookup failed"),
            "{error:#}"
        );
    }

    #[test]
    fn retirement_rolls_back_late_trigger_failure() {
        let mut fixture = fixture();
        let before = snapshot(&fixture.store.conn, "A").unwrap();
        let mut second = fixture.spec.retire[0].clone();
        second.id = "B".into();
        fixture.spec.retire.push(second);
        fixture.store.conn.execute_batch("CREATE TRIGGER reject_second BEFORE UPDATE ON artifacts WHEN OLD.id = 'B' BEGIN SELECT RAISE(ABORT, 'injected late failure'); END;").unwrap();
        assert!(
            fixture
                .store
                .retire_artifact_paths(&fixture.root, &fixture.spec)
                .is_err()
        );
        assert_eq!(snapshot(&fixture.store.conn, "A").unwrap(), before);
        assert_eq!(export_run_count(&fixture), 0);
    }
}
