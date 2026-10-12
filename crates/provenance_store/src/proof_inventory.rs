//! Rocq `_RocqProject` inventory loader and theorem-table rendering.
//!
//! - `load_proof_inventory(proofs_project_path)`: parses the
//!   `_RocqProject` text file, checks both proof roots against disk,
//!   computes the theorem stem, and indexes numeric prefixes only for
//!   collision reporting and identifier reservation.
//! - `load_theorems_from_inventory`: builds `Vec<TheoremRecord>` from the
//!   inventory, attaching claim-link backreferences and using the
//!   referenced claim's statement as the theorem title when one
//!   matches, else falling back to a humanized stem.
//! - `normalize_claims_against_proof_inventory`: walks the claim
//!   records, runs them through `normalize_claim_record`, recomputes
//!   the canonical formal_proof path from the inventory, and re-renders
//!   compat_toml_text if the resolved path changed.
//! - `render_theorem_markdown`: emits the canonical
//!   docs/THEOREM_REGISTRY.md table from the loaded inventory.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path},
};

use anyhow::{Context, Result, bail};
use camino::Utf8PathBuf;
use provenance_core::{ClaimRecord, TheoremRecord};
use rusqlite::{Connection, OptionalExtension};

use super::{
    ProofInventory, ProofInventoryEntry,
    claim_proofs::{
        canonical_formal_proof_for_claim, link_claims_for_proof,
        normalized_claim_id_from_theorem_stem, render_normalized_claim_compat_toml,
    },
    compat_render::compat_markdown_export_header,
    status_normalize::normalize_claim_record,
    toml_helpers::load_text,
};

pub(crate) fn load_proof_inventory(proofs_project_path: &Path) -> Result<ProofInventory> {
    if !fs::symlink_metadata(proofs_project_path)?
        .file_type()
        .is_file()
    {
        bail!("proof project must be a regular file");
    }
    let raw = load_text(proofs_project_path)?;
    let mut inventory = ProofInventory {
        project_raw: raw.clone(),
        ..ProofInventory::default()
    };
    let project_root = proofs_project_path
        .parent()
        .context("proof project has no parent")?;
    if !fs::symlink_metadata(project_root)?.file_type().is_dir() {
        bail!("proof project root must be a regular directory");
    }
    let mut listed = BTreeSet::new();
    let mut stems = BTreeMap::new();
    for (line_index, line) in raw.lines().enumerate() {
        let trimmed = line.split('#').next().unwrap_or_default().trim();
        if trimmed.is_empty() || trimmed.starts_with('-') {
            continue;
        }
        let relative = Path::new(trimmed);
        if !trimmed.ends_with(".v")
            || trimmed.split_whitespace().count() != 1
            || !matches!(relative.components().next(), Some(Component::Normal(root)) if root == "theories" || root == "verified")
            || relative
                .components()
                .any(|part| !matches!(part, Component::Normal(_)))
        {
            bail!(
                "invalid proof project source at line {}: {trimmed}",
                line_index + 1
            );
        }
        if !listed.insert(trimmed.to_owned()) {
            bail!("duplicate proof project source: {trimmed}");
        }
        let path = Utf8PathBuf::from(format!("proofs/{trimmed}"));
        let stem = Path::new(trimmed)
            .file_stem()
            .and_then(|value| value.to_str())
            .unwrap_or(trimmed)
            .to_string();
        let entry = ProofInventoryEntry {
            stem: stem.clone(),
            path,
        };
        if let Some(previous) = stems.insert(stem.clone(), trimmed.to_owned()) {
            bail!("proof legacy-name collision {stem}: {previous}, {trimmed}");
        }
        if let Some(claim_id) = normalized_claim_id_from_theorem_stem(&stem) {
            inventory
                .verified_by_claim_id
                .entry(claim_id)
                .or_default()
                .push(entry.clone());
        }
        inventory.source_entries.push(entry);
    }
    if listed.is_empty() {
        bail!("proof project contains no source entries");
    }
    let mut actual = BTreeSet::new();
    for root in ["theories", "verified"] {
        let directory = project_root.join(root);
        if directory.exists() {
            collect_sources(project_root, &directory, &mut actual)?;
        }
    }
    let missing = listed.difference(&actual).cloned().collect::<Vec<_>>();
    let unlisted = actual.difference(&listed).cloned().collect::<Vec<_>>();
    if !missing.is_empty() || !unlisted.is_empty() {
        bail!(
            "proof source inventory mismatch; missing listed sources: {missing:?}; unlisted disk sources: {unlisted:?}"
        );
    }
    Ok(inventory)
}

fn collect_sources(root: &Path, directory: &Path, sources: &mut BTreeSet<String>) -> Result<()> {
    if !fs::symlink_metadata(directory)?.file_type().is_dir() {
        bail!(
            "proof source root must be a regular directory: {}",
            directory.display()
        );
    }
    for entry in fs::read_dir(directory)
        .with_context(|| format!("read proof directory {}", directory.display()))?
    {
        let entry = entry?;
        let path = entry.path();
        let kind = entry.file_type()?;
        if kind.is_symlink() {
            bail!("proof inventory rejects symbolic link {}", path.display());
        }
        if kind.is_dir() {
            collect_sources(root, &path, sources)?;
        } else if path.extension().is_some_and(|extension| extension == "v") {
            if !kind.is_file() {
                bail!("proof source is not a regular file: {}", path.display());
            }
            let relative = path
                .strip_prefix(root)?
                .to_str()
                .context("proof source path is not UTF-8")?;
            sources.insert(relative.to_owned());
        }
    }
    Ok(())
}

pub(crate) fn load_theorems_from_inventory(
    connection: &Connection,
    repo_root: &Path,
    proof_inventory: &ProofInventory,
    claims: &[ClaimRecord],
) -> Result<Vec<TheoremRecord>> {
    let mut out = Vec::new();
    for entry in &proof_inventory.source_entries {
        let mut linked_claim_ids = link_claims_for_proof(&entry.path, &entry.stem, claims);
        let mut title = claims
            .iter()
            .find(|claim| linked_claim_ids.iter().any(|id| id == &claim.id))
            .map(|claim| claim.statement.clone())
            .unwrap_or_else(|| entry.stem.replace('_', " "));
        if !repo_root.join(entry.path.as_str()).is_file() {
            bail!("listed proof source disappeared: {}", entry.path);
        }
        let existing = connection.query_row(
            "SELECT theorems.title, theorem_identities.proof_path, theorem_identities.stable_id, theorem_identities.identity_kind, theorems.linked_claim_ids_json FROM theorem_identities LEFT JOIN theorems ON theorems.id=theorem_identities.legacy_name WHERE theorem_identities.legacy_name=?1",
            [&entry.stem],
            |row| Ok((row.get::<_, Option<String>>(0)?, row.get::<_, String>(1)?, row.get::<_,String>(2)?, row.get::<_,String>(3)?, row.get::<_,Option<String>>(4)?)),
        ).optional()?;
        let mut status = super::theorem_execution::SOURCE_ONLY.to_owned();
        let mut identity_kind = if linked_claim_ids.is_empty() {
            "unresolved"
        } else {
            "explicit_link"
        }
        .to_owned();
        let mut stable_id = super::theorem_identity::default_stable_theorem_id(&entry.stem);
        if let Some((retained_title, retained_path, retained_id, retained_kind, retained_links)) =
            existing
        {
            if retained_path != entry.path.as_str() {
                bail!(
                    "proof locator collision for {}: {retained_path}, {}",
                    entry.stem,
                    entry.path
                );
            }
            if let Some(retained_title) = retained_title {
                title = retained_title;
            }
            stable_id = retained_id;
            identity_kind = retained_kind;
            if let Some(retained_links) = retained_links {
                linked_claim_ids = serde_json::from_str(&retained_links)
                    .context("parse retained theorem claim links")?;
            }
            if super::theorem_execution::kernel_witness_matches(
                connection,
                repo_root,
                &stable_id,
                &entry.path,
            )? {
                status = super::theorem_execution::KERNEL_CHECKED.to_owned();
            }
        }
        out.push(TheoremRecord {
            id: stable_id,
            legacy_name: entry.stem.clone(),
            title,
            proof_path: entry.path.clone(),
            status,
            identity_kind,
            linked_claim_ids,
            source: "_RocqProject".to_string(),
        });
    }
    Ok(out)
}

pub(crate) fn normalize_claims_against_proof_inventory(
    repo_root: &Path,
    claims: &mut [ClaimRecord],
    proof_inventory: &ProofInventory,
) -> Result<()> {
    for claim in claims {
        normalize_claim_record(claim)?;
        let canonical_formal_proof =
            canonical_formal_proof_for_claim(repo_root, claim, proof_inventory);
        if claim.formal_proof != canonical_formal_proof {
            claim.formal_proof = canonical_formal_proof;
            claim.compat_toml_text = render_normalized_claim_compat_toml(claim)?;
        }
    }
    Ok(())
}

pub(crate) fn render_theorem_markdown(source_label: &str, theorems: &[TheoremRecord]) -> String {
    let mut lines = compat_markdown_export_header(source_label);
    lines.extend([
        "# Theorems".to_string(),
        String::new(),
        format!(
            "This file is generated from the canonical SQLite control plane and currently indexes {} Rocq proof files.",
            theorems.len()
        ),
        String::new(),
        "| Stable Theorem ID | Legacy Name | Proof File | Status | Identity Kind | Linked Claims |".to_string(),
        "|---|---|---|---|---|---|".to_string(),
    ]);
    for theorem in theorems {
        let claims = if theorem.linked_claim_ids.is_empty() {
            "-".to_string()
        } else {
            theorem.linked_claim_ids.join(", ")
        };
        lines.push(format!(
            "| `{}` | `{}` | `{}` | {} | {} | {} |",
            theorem.id,
            theorem.legacy_name,
            theorem.proof_path,
            theorem.status,
            theorem.identity_kind,
            claims
        ));
    }
    lines.push(String::new());
    lines.join("\n")
}
