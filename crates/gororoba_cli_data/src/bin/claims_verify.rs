//! Claims verification runner.
//!
//! Replaces 11 Python verification scripts with a single Rust binary.
//! Runs all checks and exits with code 0 (pass) or 2 (fail).
//!
//! Usage:
//!   claims-verify                           # all checks
//!   claims-verify --check metadata          # just matrix metadata
//!   claims-verify --check evidence          # just evidence links
//!   claims-verify --check where-stated      # just Where stated pointers
//!   claims-verify --check tasks             # tasks metadata + consistency
//!   claims-verify --check domains           # domain mapping
//!   claims-verify --check providers         # dataset manifest vs source

use clap::Parser;
use std::{path::PathBuf, process};

use gororoba_cli::claims::{
    schema::{is_toml_canonical_status, normalize_status},
    verify,
};
use provenance_store::{ControlPlaneCompatKind, ProvenanceStore};

#[derive(Parser)]
#[command(
    name = "claims-verify",
    about = "Verify claims infrastructure integrity"
)]
struct Cli {
    /// Repository root directory.
    #[arg(long, default_value = ".")]
    repo_root: PathBuf,

    /// Legacy claims matrix path (used only as a fallback compatibility input).
    #[arg(long, default_value = "docs/CLAIMS_EVIDENCE_MATRIX.md")]
    matrix: String,

    /// Canonical SQLite database path.
    #[arg(long, default_value = "registry/canonical/control_plane.sqlite3")]
    db: String,

    /// Specific check to run (default: all).
    #[arg(long, value_parser = ["metadata", "evidence", "where-stated", "tasks", "domains", "providers", "all"])]
    check: Option<String>,
}

fn run_check(name: &str, failures: Vec<String>) -> bool {
    if failures.is_empty() {
        eprintln!("OK: {name}");
        true
    } else {
        for (i, msg) in failures.iter().enumerate() {
            if i < 50 {
                eprintln!("FAIL [{name}]: {msg}");
            }
        }
        if failures.len() > 50 {
            eprintln!("... plus {} more failures", failures.len() - 50);
        }
        eprintln!("FAIL: {name} ({} issues)", failures.len());
        false
    }
}

fn main() {
    let cli = Cli::parse();
    let repo_root = cli.repo_root.canonicalize().unwrap_or_else(|e| {
        eprintln!("ERROR: Cannot resolve repo root {:?}: {e}", cli.repo_root);
        process::exit(2);
    });

    let check_type = cli.check.as_deref().unwrap_or("all");
    let db_path = repo_root.join(&cli.db);

    let read_claims_compat_text = || -> String {
        if db_path.exists()
            && let Ok(mut store) = ProvenanceStore::open_read_only(&db_path)
            && let Ok(text) = store.control_plane_compat_text(ControlPlaneCompatKind::Claims)
        {
            return text;
        }
        let matrix_path = repo_root.join(&cli.matrix);
        if !matrix_path.exists() {
            eprintln!(
                "ERROR: Missing canonical DB compatibility export and legacy matrix fallback: {}",
                matrix_path.display()
            );
            process::exit(2);
        }
        std::fs::read_to_string(&matrix_path).unwrap_or_else(|e| {
            eprintln!("ERROR: Cannot read legacy matrix fallback: {e}");
            process::exit(2);
        })
    };

    // Recorded `proofs/` paths resolve against the gororoba-math checkout that
    // GOROROBA_MATH names; without it those checks are skipped and counted.
    let proof_tree = repo_root::ProofTree::from_environment_if_set().unwrap_or_else(|error| {
        eprintln!("ERROR: resolve the proof tree: {error}");
        process::exit(2);
    });
    let mut all_ok = true;

    match check_type {
        "all" => {
            let mut failures = Vec::new();
            let mut summaries = Vec::new();

            let db_failures = match open_claim_store(&db_path) {
                Ok(store) => {
                    let mut combined = Vec::new();
                    let metadata = verify_claim_metadata_from_db(&store);
                    summaries.push(format!("claim_metadata_sqlite: {} issues", metadata.len()));
                    combined.extend(metadata);
                    let where_stated = verify_claim_where_stated_from_db(&store);
                    summaries.push(format!(
                        "claim_where_stated_sqlite: {} issues",
                        where_stated.len()
                    ));
                    combined.extend(where_stated);
                    let evidence = verify_claim_evidence_links_from_db(
                        &repo_root,
                        proof_tree.as_ref(),
                        &store,
                    );
                    summaries.push(format!(
                        "claim_evidence_sqlite: {} issues, {} proof-source checks skipped",
                        evidence.failures.len(),
                        evidence.skipped
                    ));
                    report_skipped_proof_checks(evidence.skipped);
                    combined.extend(evidence.failures);
                    combined
                }
                Err(err) => vec![err],
            };
            failures.extend(db_failures);

            let tasks_path = repo_root.join("docs/CLAIMS_TASKS.md");
            if tasks_path.exists()
                && let Ok(tasks_text) = std::fs::read_to_string(&tasks_path)
            {
                let f = verify::verify_tasks_metadata(&tasks_text);
                summaries.push(format!("tasks_metadata: {} issues", f.len()));
                failures.extend(f);
                let f = verify::verify_task_artifact_links(&tasks_text, &repo_root);
                summaries.push(format!("task_artifacts: {} issues", f.len()));
                failures.extend(f);
            }

            let domain_path = repo_root.join("docs/claims/CLAIMS_DOMAIN_MAP.csv");
            if domain_path.exists() {
                let matrix_text = read_claims_compat_text();
                if let Ok(csv_text) = std::fs::read_to_string(&domain_path) {
                    let f = verify::verify_domain_mapping(&matrix_text, &csv_text);
                    summaries.push(format!("domain_mapping: {} issues", f.len()));
                    failures.extend(f);
                }
            }

            if failures.is_empty() {
                eprintln!("OK: all verification checks passed");
                eprintln!("{}", summaries.join("\n"));
            } else {
                for (i, msg) in failures.iter().enumerate() {
                    if i < 100 {
                        eprintln!("FAIL: {msg}");
                    }
                }
                if failures.len() > 100 {
                    eprintln!("... plus {} more", failures.len() - 100);
                }
                eprintln!("\nTotal failures: {}", failures.len());
                all_ok = false;
            }
        }
        "metadata" => {
            let f = match open_claim_store(&db_path) {
                Ok(store) => verify_claim_metadata_from_db(&store),
                Err(err) => vec![err],
            };
            if !run_check("matrix_metadata", f) {
                all_ok = false;
            }
        }
        "evidence" => {
            let f = match open_claim_store(&db_path) {
                Ok(store) => {
                    let evidence = verify_claim_evidence_links_from_db(
                        &repo_root,
                        proof_tree.as_ref(),
                        &store,
                    );
                    report_skipped_proof_checks(evidence.skipped);
                    evidence.failures
                }
                Err(err) => vec![err],
            };
            if !run_check("evidence_links", f) {
                all_ok = false;
            }
        }
        "where-stated" => {
            let f = match open_claim_store(&db_path) {
                Ok(store) => verify_claim_where_stated_from_db(&store),
                Err(err) => vec![err],
            };
            if !run_check("where_stated", f) {
                all_ok = false;
            }
        }
        "tasks" => {
            let matrix_text = read_claims_compat_text();
            let tasks_path = repo_root.join("docs/CLAIMS_TASKS.md");
            if tasks_path.exists() {
                if let Ok(tasks_text) = std::fs::read_to_string(&tasks_path) {
                    let f = verify::verify_tasks_metadata(&tasks_text);
                    if !run_check("tasks_metadata", f) {
                        all_ok = false;
                    }
                    let f = verify::verify_tasks_consistency(&matrix_text, &tasks_text);
                    if !run_check("tasks_consistency", f) {
                        all_ok = false;
                    }
                    let f = verify::verify_task_artifact_links(&tasks_text, &repo_root);
                    if !run_check("task_artifacts", f) {
                        all_ok = false;
                    }
                }
            } else {
                eprintln!("SKIP: docs/CLAIMS_TASKS.md not found");
            }
        }
        "domains" => {
            let matrix_text = read_claims_compat_text();
            let domain_path = repo_root.join("docs/claims/CLAIMS_DOMAIN_MAP.csv");
            if domain_path.exists() {
                if let Ok(csv_text) = std::fs::read_to_string(&domain_path) {
                    let f = verify::verify_domain_mapping(&matrix_text, &csv_text);
                    if !run_check("domain_mapping", f) {
                        all_ok = false;
                    }
                }
            } else {
                eprintln!("SKIP: docs/claims/CLAIMS_DOMAIN_MAP.csv not found");
            }
        }
        "providers" => {
            let registry_path = repo_root.join("registry/external_sources.toml");
            let fetch_path = repo_root.join("crates/gororoba_cli_data/src/bin/fetch_datasets.rs");

            if !registry_path.exists() {
                eprintln!("ERROR: Missing registry/external_sources.toml");
                all_ok = false;
            }
            if !fetch_path.exists() {
                eprintln!("ERROR: Missing crates/gororoba_cli_data/src/bin/fetch_datasets.rs");
                all_ok = false;
            }

            if all_ok {
                let registry_text = match std::fs::read_to_string(&registry_path) {
                    Ok(t) => t,
                    Err(e) => {
                        eprintln!("ERROR: Cannot read registry/external_sources.toml: {e}");
                        process::exit(2);
                    }
                };
                let fetch_src = match std::fs::read_to_string(&fetch_path) {
                    Ok(t) => t,
                    Err(e) => {
                        eprintln!(
                            "ERROR: Cannot read crates/gororoba_cli_data/src/bin/fetch_datasets.rs: {e}"
                        );
                        process::exit(2);
                    }
                };

                let chk = verify::verify_dataset_providers(&registry_text, &fetch_src);
                for w in chk.warnings.iter().take(50) {
                    eprintln!("WARN [dataset_providers]: {w}");
                }
                if chk.warnings.len() > 50 {
                    eprintln!(
                        "WARN [dataset_providers]: ... plus {} more warnings",
                        chk.warnings.len() - 50
                    );
                }
                if !run_check("dataset_providers", chk.failures) {
                    all_ok = false;
                }
            }
        }
        _ => unreachable!("clap validates check type"),
    }

    if all_ok {
        process::exit(0);
    } else {
        process::exit(2);
    }
}

fn open_claim_store(db_path: &std::path::Path) -> Result<ProvenanceStore, String> {
    if !db_path.exists() {
        return Err(format!(
            "Missing canonical SQLite database: {}. Run `provenance import-legacy-control-plane` first.",
            db_path.display()
        ));
    }
    ProvenanceStore::open_read_only(db_path)
        .map_err(|err| format!("open {}: {err}", db_path.display()))
}

fn verify_claim_metadata_from_db(store: &ProvenanceStore) -> Vec<String> {
    let mut failures = Vec::new();
    let claims = match store.list_claims() {
        Ok(rows) => rows,
        Err(err) => return vec![format!("load claims from SQLite: {err}")],
    };
    for claim in claims {
        if claim.status.trim().is_empty() {
            failures.push(format!("{}: status is empty", claim.id));
        } else {
            let (normalized, _) = normalize_status(claim.status.trim());
            let legacy_ok = matches!(
                claim.status.trim(),
                "Pending"
                    | "Open"
                    | "Active"
                    | "Falsified"
                    | "Speculative"
                    | "Conjecture"
                    | "Closed/Verified"
                    | "Closed/Falsified"
                    | "Closed/Methodology-Mismatch"
                    | "Deferred"
                    | "Proposed"
            );
            if !is_toml_canonical_status(claim.status.trim())
                && !is_toml_canonical_status(&normalized)
                && !legacy_ok
            {
                failures.push(format!(
                    "{}: non-canonical TOML status {:?}",
                    claim.id, claim.status
                ));
            }
        }
        let last_verified = claim.last_verified.trim();
        if !last_verified.is_empty()
            && (last_verified.len() < 10
                || !last_verified
                    .chars()
                    .take(10)
                    .enumerate()
                    .all(|(idx, ch)| match idx {
                        4 | 7 => ch == '-',
                        _ => ch.is_ascii_digit(),
                    }))
        {
            failures.push(format!(
                "{}: last_verified must begin with ISO date YYYY-MM-DD (got: {:?})",
                claim.id, claim.last_verified
            ));
        }
    }
    failures
}

fn verify_claim_where_stated_from_db(store: &ProvenanceStore) -> Vec<String> {
    let mut failures = Vec::new();
    let claims = match store.list_claims() {
        Ok(rows) => rows,
        Err(err) => return vec![format!("load claims from SQLite: {err}")],
    };
    for claim in claims {
        let ws = claim.where_stated.trim();
        // A "stable path pointer" is any of:
        //   - a backtick-quoted fragment (code span referencing a path)
        //   - a known repo-relative path prefix
        //   - an experiment ID reference (E-NNN or multiple E-refs)
        //   - a URL reference (http/https for external evidence)
        //   - the sentinel "multiple docs" for cross-cutting claims
        let has_path = ws.contains('`')
            || ws.contains("src/")
            || ws.contains("docs/")
            || ws.contains("data/")
            || ws.contains("crates/")
            || ws.contains("proofs/")
            || ws.contains("registry/")
            || ws.contains("experiments/")
            || ws.contains("multiple docs")
            || ws.contains("http://")
            || ws.contains("https://")
            || ws.contains("github.com/")
            // Experiment-ID-only references: "E-NNN" is a stable pointer into registry/experiments.toml
            || (ws.contains("E-") && ws.chars().nth(ws.find("E-").unwrap_or(0) + 2).map(|c| c.is_ascii_digit()).unwrap_or(false));
        if !has_path {
            failures.push(format!(
                "{}: missing stable path pointer in where_stated",
                claim.id
            ));
        }
    }
    failures
}

/// Returns true if `path` (relative to `repo_root`) is listed in .gitignore.
///
/// WHY: This repo intentionally gitignores data/csv/ (runtime output) and most
/// docs/*.md (generated/ephemeral). Checking for their on-disk existence would
/// produce false positives for any claim that references these paths.
fn is_gitignored(repo_root: &std::path::Path, path: &str) -> bool {
    std::process::Command::new("git")
        .args(["check-ignore", "-q", path])
        .current_dir(repo_root)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Failures of the evidence-link check, and the number of proof-source checks
/// that did not run because no proof tree was resolved.
struct EvidenceLinkChecks {
    failures: Vec<String>,
    skipped: usize,
}

/// Prints the count of skipped proof-source checks; a skip is reported apart
/// from the passes and never counted as one.
fn report_skipped_proof_checks(skipped: usize) {
    if skipped > 0 {
        eprintln!(
            "SKIP: {skipped} proof-source checks did not run: GOROROBA_MATH is unset, so recorded proofs/ paths were not read"
        );
    }
}

/// Checks one recorded path. A `proofs/` locator is read from the proof tree
/// (a skip without one); any other path is read below the repository root,
/// where a path that git ignores is allowed to be absent. Both kinds refuse a
/// path that leaves its directory.
fn check_recorded_path(
    repo_root: &std::path::Path,
    proof_tree: Option<&repo_root::ProofTree>,
    recorded: &str,
    allow_ignored: bool,
    failures: &mut Vec<String>,
    skipped: &mut usize,
    label: &str,
) {
    if repo_root::proof_tree::recorded_relative(recorded).is_some() {
        match proof_tree {
            None => *skipped += 1,
            Some(tree) => match tree.exists(repo_root, recorded) {
                Ok(true) => {}
                Ok(false) => failures.push(format!("{label}: missing proof path {recorded}")),
                Err(error) => failures.push(format!("{label}: proof path is refused: {error}")),
            },
        }
        return;
    }
    match repo_root::proof_tree::resolve_below(repo_root, recorded, recorded) {
        Ok(path) => {
            if !path.exists() && !(allow_ignored && is_gitignored(repo_root, recorded)) {
                failures.push(format!("{label}: missing referenced path {recorded}"));
            }
        }
        Err(error) => failures.push(format!("{label}: referenced path is refused: {error}")),
    }
}

fn verify_claim_evidence_links_from_db(
    repo_root: &std::path::Path,
    proof_tree: Option<&repo_root::ProofTree>,
    store: &ProvenanceStore,
) -> EvidenceLinkChecks {
    let mut failures = Vec::new();
    let mut skipped = 0;
    let claims = match store.list_claims() {
        Ok(rows) => rows,
        Err(err) => {
            return EvidenceLinkChecks {
                failures: vec![format!("load claims from SQLite: {err}")],
                skipped,
            };
        }
    };
    for claim in claims {
        for path in extract_backtick_paths(&claim.where_stated) {
            check_recorded_path(
                repo_root,
                proof_tree,
                &path,
                true,
                &mut failures,
                &mut skipped,
                &claim.id,
            );
        }
    }
    // verify_control_plane_invariants owns the formal_proof existence rule,
    // including the non-path dispositions that is_formal_proof_disposition
    // admits.
    let theorems = match store.list_theorems() {
        Ok(rows) => rows,
        Err(err) => {
            return EvidenceLinkChecks {
                failures: vec![format!("load theorems from SQLite: {err}")],
                skipped,
            };
        }
    };
    for theorem in theorems {
        check_recorded_path(
            repo_root,
            proof_tree,
            theorem.proof_path.as_str(),
            false,
            &mut failures,
            &mut skipped,
            &theorem.id,
        );
    }
    EvidenceLinkChecks { failures, skipped }
}

fn extract_backtick_paths(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut current = String::new();
    let mut in_tick = false;
    for ch in text.chars() {
        if ch == '`' {
            if in_tick {
                let trimmed = current.trim();
                if trimmed.starts_with("crates/")
                    || trimmed.starts_with("docs/")
                    || trimmed.starts_with("data/")
                    || trimmed.starts_with("proofs/")
                    || trimmed.starts_with("registry/")
                    || trimmed.starts_with("src/")
                {
                    out.push(trimmed.to_string());
                }
                current.clear();
            }
            in_tick = !in_tick;
            continue;
        }
        if in_tick {
            current.push(ch);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(
        repository: &std::path::Path,
        tree: Option<&repo_root::ProofTree>,
        recorded: &str,
    ) -> (Vec<String>, usize) {
        let mut failures = Vec::new();
        let mut skipped = 0;
        check_recorded_path(
            repository,
            tree,
            recorded,
            false,
            &mut failures,
            &mut skipped,
            "T",
        );
        (failures, skipped)
    }

    #[test]
    fn proof_paths_are_read_from_the_tree_and_skipped_without_one() {
        let directory =
            std::env::temp_dir().join(format!("gororoba-claims-verify-{}", std::process::id()));
        let tree_root = directory.join("tree");
        let repository = directory.join("repository");
        std::fs::create_dir_all(tree_root.join("verified")).unwrap();
        std::fs::create_dir_all(repository.join("docs")).unwrap();
        std::fs::write(tree_root.join("_RocqProject"), "").unwrap();
        std::fs::write(tree_root.join("verified/C001_Test.v"), "").unwrap();
        std::fs::write(repository.join("docs/kept.md"), "").unwrap();
        let tree = repo_root::ProofTree::at_root(&tree_root).unwrap();

        assert_eq!(
            check(&repository, Some(&tree), "proofs/verified/C001_Test.v"),
            (vec![], 0)
        );
        assert_eq!(
            check(&repository, None, "proofs/verified/C001_Test.v"),
            (vec![], 1)
        );
        assert_eq!(check(&repository, None, "docs/kept.md"), (vec![], 0));
        assert_eq!(check(&repository, Some(&tree), "docs/kept.md"), (vec![], 0));
        for recorded in [
            "proofs/verified/Absent.v",
            "proofs/../x.v",
            "docs/missing.md",
            "docs/../../x",
            "/etc/passwd",
        ] {
            let (failures, skipped) = check(&repository, Some(&tree), recorded);
            assert_eq!(
                (failures.len(), skipped),
                (1, 0),
                "{recorded}: {failures:?}"
            );
        }
        let (failures, _) = check(&repository, None, "docs/../../x");
        assert_eq!(failures.len(), 1);
        std::fs::remove_dir_all(&directory).unwrap();
    }
}
