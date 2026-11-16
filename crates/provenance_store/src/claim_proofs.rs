//! Claim <-> Rocq proof correlation and compat-export rendering for
//! individual claim/insight rows.
//!
//! - `canonical_formal_proof_for_claim`: resolves the canonical
//!   `formal_proof` path for a claim by checking the claim's own
//!   formal_proof field, scanning where_stated/status_note/formal_proof
//!   for `proofs/.../*.v` references. A missing explicit path remains
//!   unresolved.
//! - `render_normalized_claim_compat_toml`: re-emits a ClaimRecord into
//!   compat_toml_text, splicing live SQLite columns.
//! - `render_normalized_insight_compat_toml`: re-emits an insight TOML
//!   table with the normalized status token applied.
//! - `extract_proof_paths`: scrapes `proofs/...*.v` paths from a text
//!   blob (where_stated / status_note / formal_proof).
//! - `link_claims_for_proof`: enumerates ClaimRecord ids that explicitly
//!   reference a given proof path.
//! - `normalized_claim_id_from_theorem_stem`: parses a numeric prefix for
//!   reservation and collision reporting only.

use anyhow::{Context, Result};
use camino::Utf8PathBuf;
use provenance_core::ClaimRecord;
use toml::Value;

use super::{
    ProofInventory, status_normalize::normalize_insight_status, theorem_execution::EvidenceRoots,
    toml_helpers::render_toml_table,
};

/// An explicit non-path disposition of the `formal_proof` field. The field
/// schema admits `na_empirical[:rationale]`, `na_observational[:source]`,
/// `na_methodology[:tool]`, `pending[:reason]` and `external:<citation>`
/// beside proof paths. A reindex keeps these verbatim instead of resolving
/// them against the proof tree, so a reviewer's decision that a claim has
/// no proof survives `provenance index-control-plane`, and the
/// numeric-prefix backfill sees a populated field and never relinks an
/// unrelated proof file.
pub fn is_formal_proof_disposition(value: &str) -> bool {
    let value = value.trim();
    [
        "na_empirical",
        "na_observational",
        "na_methodology",
        "pending",
    ]
    .iter()
    .any(|prefix| {
        value == *prefix
            || value
                .strip_prefix(prefix)
                .is_some_and(|rest| rest.starts_with(':'))
    }) || value.starts_with("external:")
}

pub(crate) fn canonical_formal_proof_for_claim(
    roots: EvidenceRoots<'_>,
    claim: &ClaimRecord,
    _proof_inventory: &ProofInventory,
) -> Result<Option<String>> {
    if let Some(formal_proof) = claim.formal_proof.as_deref()
        && !formal_proof.trim().is_empty()
        && (is_formal_proof_disposition(formal_proof)
            || roots
                .exists(formal_proof)
                .with_context(|| format!("claim {} formal_proof", claim.id))?)
    {
        return Ok(Some(formal_proof.trim().to_string()));
    }

    let mut referenced_paths = extract_proof_paths(&claim.where_stated);
    if let Some(status_note) = &claim.status_note {
        referenced_paths.extend(extract_proof_paths(status_note));
    }
    if let Some(formal_proof) = claim.formal_proof.as_deref() {
        referenced_paths.extend(extract_proof_paths(formal_proof));
    }
    let mut existing_paths = Vec::new();
    for path in referenced_paths {
        if roots
            .exists(&path)
            .with_context(|| format!("claim {} proof reference", claim.id))?
        {
            existing_paths.push(path);
        }
    }
    existing_paths.sort();
    existing_paths.dedup();

    if existing_paths.len() == 1 {
        return Ok(existing_paths.into_iter().next());
    }

    Ok(None)
}

pub(crate) fn render_normalized_claim_compat_toml(row: &ClaimRecord) -> Result<String> {
    let mut table = if row.compat_toml_text.trim().is_empty() {
        let mut table = toml::map::Map::new();
        table.insert("id".to_string(), Value::String(row.id.clone()));
        table.insert(
            "statement".to_string(),
            Value::String(row.statement.clone()),
        );
        table.insert("status".to_string(), Value::String(row.status.clone()));
        table.insert(
            "where_stated".to_string(),
            Value::String(row.where_stated.clone()),
        );
        table.insert(
            "last_verified".to_string(),
            Value::String(row.last_verified.clone()),
        );
        if let Some(status_note) = &row.status_note {
            table.insert(
                "status_note".to_string(),
                Value::String(status_note.clone()),
            );
        }
        table
    } else {
        toml::from_str::<toml::map::Map<String, Value>>(&row.compat_toml_text)
            .context("parse normalized claim compat row")?
    };
    table.insert("status".to_string(), Value::String(row.status.clone()));
    match &row.status_note {
        Some(status_note) if !status_note.trim().is_empty() => {
            table.insert(
                "status_note".to_string(),
                Value::String(status_note.clone()),
            );
        }
        _ => {
            table.remove("status_note");
        }
    }
    match &row.formal_proof {
        Some(formal_proof) if !formal_proof.trim().is_empty() => {
            table.insert(
                "formal_proof".to_string(),
                Value::String(formal_proof.clone()),
            );
        }
        _ => {
            table.remove("formal_proof");
        }
    }
    render_toml_table(&table)
}

pub(crate) fn render_normalized_insight_compat_toml(
    table: &toml::map::Map<String, Value>,
    raw_status: Option<&str>,
) -> Result<String> {
    let mut table = table.clone();
    match raw_status.map(normalize_insight_status) {
        Some(status) if !status.trim().is_empty() => {
            table.insert("status".to_string(), Value::String(status.to_string()));
        }
        _ => {
            table.remove("status");
        }
    }
    render_toml_table(&table)
}

pub(crate) fn extract_proof_paths(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cursor = text;
    while let Some(start) = cursor.find("proofs/") {
        let candidate = &cursor[start..];
        let mut end = 0usize;
        for ch in candidate.chars() {
            if ch.is_ascii_alphanumeric() || matches!(ch, '/' | '_' | '-' | '.') {
                end += ch.len_utf8();
            } else {
                break;
            }
        }
        let path = candidate[..end].trim_matches('`').trim_matches('"').trim();
        if path.ends_with(".v") {
            out.push(path.to_string());
        }
        cursor = &candidate[end..];
    }
    out
}

pub(crate) fn link_claims_for_proof(
    proof_path: &Utf8PathBuf,
    _stem: &str,
    claims: &[ClaimRecord],
) -> Vec<String> {
    let proof_path_str = proof_path.as_str();
    let mut out = Vec::new();
    for claim in claims {
        let matches = claim
            .formal_proof
            .as_deref()
            .map(|path| path.trim() == proof_path_str)
            .unwrap_or(false)
            || claim.where_stated.contains(proof_path_str)
            || claim
                .status_note
                .as_deref()
                .map(|note| note.contains(proof_path_str))
                .unwrap_or(false);
        if matches {
            out.push(claim.id.clone());
        }
    }
    out.sort();
    out.dedup();
    out
}

pub(crate) fn normalized_claim_id_from_theorem_stem(stem: &str) -> Option<String> {
    let suffix = stem.strip_prefix('C')?;
    let digits = suffix
        .chars()
        .take_while(|ch| ch.is_ascii_digit())
        .collect::<String>();
    if digits.is_empty() {
        return None;
    }
    Some(format!("C-{digits}"))
}

#[cfg(test)]
mod tests {
    use super::{
        EvidenceRoots, ProofInventory, canonical_formal_proof_for_claim, link_claims_for_proof,
    };
    use camino::Utf8PathBuf;
    use provenance_core::ClaimRecord;

    struct TreeFixture {
        directory: std::path::PathBuf,
        tree: repo_root::ProofTree,
    }

    impl TreeFixture {
        fn new(name: &str) -> Self {
            let directory = std::env::temp_dir().join(format!(
                "gororoba-claim-proofs-{name}-{}",
                std::process::id()
            ));
            let tree_root = directory.join("tree");
            std::fs::create_dir_all(tree_root.join("verified")).unwrap();
            std::fs::write(tree_root.join("_RocqProject"), "").unwrap();
            std::fs::write(tree_root.join("verified/C001_Test.v"), "").unwrap();
            let tree = repo_root::ProofTree::at_root(tree_root).unwrap();
            Self { directory, tree }
        }
    }

    impl Drop for TreeFixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.directory);
        }
    }

    fn claim_with(formal_proof: Option<&str>, where_stated: &str) -> ClaimRecord {
        ClaimRecord {
            id: "C-001".to_string(),
            statement: "statement".to_string(),
            status: "Verified".to_string(),
            where_stated: where_stated.to_string(),
            last_verified: "2026-11-14".to_string(),
            formal_proof: formal_proof.map(str::to_string),
            status_note: None,
            compat_toml_text: String::new(),
        }
    }

    #[test]
    fn a_refused_proof_path_is_an_error_not_an_absent_file() {
        let fixture = TreeFixture::new("refused");
        let repository = fixture.directory.join("repository");
        std::fs::create_dir_all(&repository).unwrap();
        let roots = EvidenceRoots::new(&repository, &fixture.tree);
        let inventory = ProofInventory::default();
        for claim in [
            claim_with(Some("proofs/../x.v"), ""),
            claim_with(None, "see proofs/../x.v"),
            claim_with(Some("/etc/passwd"), ""),
        ] {
            assert!(
                canonical_formal_proof_for_claim(roots, &claim, &inventory).is_err(),
                "{claim:?}"
            );
        }
        let kept = claim_with(Some("proofs/verified/C001_Test.v"), "");
        assert_eq!(
            canonical_formal_proof_for_claim(roots, &kept, &inventory).unwrap(),
            Some("proofs/verified/C001_Test.v".to_string())
        );
        let missing = claim_with(Some("proofs/verified/Absent.v"), "");
        assert_eq!(
            canonical_formal_proof_for_claim(roots, &missing, &inventory).unwrap(),
            None
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_proof_path_through_a_link_out_of_the_tree_is_an_error() {
        let fixture = TreeFixture::new("link");
        let repository = fixture.directory.join("repository");
        let outside = fixture.directory.join("outside");
        std::fs::create_dir_all(&repository).unwrap();
        std::fs::create_dir_all(&outside).unwrap();
        std::fs::write(outside.join("Secret.v"), "").unwrap();
        std::os::unix::fs::symlink(&outside, fixture.tree.root().join("theories")).unwrap();
        let roots = EvidenceRoots::new(&repository, &fixture.tree);
        let claim = claim_with(Some("proofs/theories/Secret.v"), "");
        assert!(
            canonical_formal_proof_for_claim(roots, &claim, &ProofInventory::default()).is_err()
        );
    }

    #[test]
    fn numeric_theorem_prefix_does_not_link_an_unrelated_claim() {
        let claim = ClaimRecord {
            id: "C-1635".to_string(),
            statement: "tensor electromagnetic Ward conformance".to_string(),
            status: "Provisional".to_string(),
            where_stated: "registry claim successor".to_string(),
            last_verified: "2026-08-04".to_string(),
            formal_proof: None,
            status_note: None,
            compat_toml_text: String::new(),
        };
        let links = link_claims_for_proof(
            &Utf8PathBuf::from("proofs/verified/C1635_SedenionDriverSemantics.v"),
            "C1635_SedenionDriverSemantics",
            &[claim],
        );
        assert!(links.is_empty());
    }

    #[test]
    fn explicit_proof_path_creates_the_only_claim_link() {
        let claim = ClaimRecord {
            id: "C-1649".to_string(),
            statement: "sedenion driver semantics".to_string(),
            status: "Verified".to_string(),
            where_stated: "proofs/verified/C1635_SedenionDriverSemantics.v".to_string(),
            last_verified: "2026-08-04".to_string(),
            formal_proof: None,
            status_note: None,
            compat_toml_text: String::new(),
        };
        let links = link_claims_for_proof(
            &Utf8PathBuf::from("proofs/verified/C1635_SedenionDriverSemantics.v"),
            "C1635_SedenionDriverSemantics",
            &[claim],
        );
        assert_eq!(links, ["C-1649"]);
    }
}
