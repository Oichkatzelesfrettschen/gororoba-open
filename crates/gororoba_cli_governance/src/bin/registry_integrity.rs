use anyhow::{Context, Result, bail};
use clap::Parser;
use provenance_store::{ControlPlaneCompatKind, ProvenanceStore};
use regex::Regex;
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};
use toml::Value;

#[derive(Parser, Debug)]
#[command(
    name = "registry-integrity",
    about = "Build or verify canonical registry-integrity lane registries"
)]
struct Args {
    #[arg(long, default_value = ".")]
    repo_root: PathBuf,
    #[arg(long, default_value = "registry/canonical/control_plane.sqlite3")]
    db: PathBuf,
    #[arg(long, default_value_t = false)]
    verify: bool,
    #[arg(long, default_value = "registry/conflict_markers.toml")]
    conflict_out: PathBuf,
    #[arg(long, default_value = "registry/lacunae.toml")]
    lacunae_out: PathBuf,
}

#[derive(Debug, Clone)]
struct ConflictMarker {
    id: String,
    marker_kind: String,
    severity: String,
    status: String,
    claim_refs: Vec<String>,
    source_registry: String,
    source_document: String,
    section_label: String,
    line_start: i64,
    line_end: i64,
    positive_evidence: Vec<String>,
    negative_evidence: Vec<String>,
    source_content_sha256: String,
    jaccard_overlap: f64,
    notes: String,
}

#[derive(Debug, Clone)]
struct Lacuna {
    id: String,
    origin: String,
    area: String,
    title: String,
    description: String,
    priority: String,
    status: String,
    claim_refs: Vec<String>,
    source_refs: Vec<String>,
    related_marker_ids: Vec<String>,
    historical_marker_ids: Vec<String>,
}

#[derive(Debug, Default, Clone)]
struct ConflictMeta {
    marker_count: usize,
    high_severity_count: usize,
    medium_severity_count: usize,
    low_severity_count: usize,
    kind_count: usize,
}

#[derive(Debug, Default, Clone)]
struct LacunaMeta {
    lacuna_count: usize,
    open_count: usize,
    high_priority_count: usize,
    medium_priority_count: usize,
    low_priority_count: usize,
    origin_kind_count: usize,
}

const POSITIVE_TERMS: &[&str] = &[
    "verified",
    "established",
    "confirmed",
    "holds",
    "consistent",
    "valid",
    "supported",
    "reproduced",
];
const NEGATIVE_TERMS: &[&str] = &[
    "refuted",
    "invalid",
    "fails",
    "contradiction",
    "inconsistent",
    "obstruction",
    "inconclusive",
    "insufficient",
];
/// Title prefix that identifies a lacuna derived from live claim status. Rows
/// carrying it are re-derived on every run, so the prefix is both the writer's
/// format and the reader's discriminator against the carried-forward set.
const CLAIM_STATUS_LACUNA_TITLE_PREFIX: &str = "Unresolved claim status for ";
const UNRESOLVED_STATUS_TOKENS: &[&str] = &[
    "PARTIAL",
    "INCONCLUSIVE",
    "THEORETICAL",
    "CLOSED_SOURCE_INSUFFICIENT",
    "CLOSED_METHODOLOGY_INSUFFICIENT",
];
const VERIFIED_STATUS_TOKENS: &[&str] = &["VERIFIED", "ESTABLISHED"];
const REFUTED_STATUS_TOKENS: &[&str] = &["REFUTED", "CLOSED_REFUTED", "CLOSED_NEGATIVE_RESULT"];
const STOPWORDS: &[&str] = &[
    "about", "across", "after", "against", "all", "also", "analysis", "being", "between", "both",
    "claim", "data", "does", "each", "from", "have", "into", "its", "model", "more", "must",
    "needs", "only", "other", "over", "results", "should", "some", "than", "their", "there",
    "these", "this", "through", "under", "using", "when", "where", "which", "while", "with",
    "without",
];

fn main() -> Result<()> {
    let args = Args::parse();
    let repo_root = args.repo_root.canonicalize().context("resolve repo root")?;
    if args.verify {
        return verify_integrity_resolution(&repo_root, &args);
    }
    build_integrity_resolution(&repo_root, &args)
}

fn build_integrity_resolution(repo_root: &Path, args: &Args) -> Result<()> {
    let claims_rows = table_array(
        &load_control_plane_registry(
            repo_root,
            &args.db,
            ControlPlaneCompatKind::Claims,
            "registry/claims.toml",
        )?,
        "claim",
    )
    .to_vec();
    let insights_rows = table_array(
        &load_control_plane_registry(
            repo_root,
            &args.db,
            ControlPlaneCompatKind::Insights,
            "registry/insights.toml",
        )?,
        "insight",
    )
    .to_vec();
    let experiments_rows = table_array(
        &load_control_plane_registry(
            repo_root,
            &args.db,
            ControlPlaneCompatKind::Experiments,
            "registry/experiments.toml",
        )?,
        "experiment",
    )
    .to_vec();
    let docs_root_rows = table_array(
        &load_toml(&repo_root.join("registry/docs_root_narratives.toml"))?,
        "document",
    )
    .to_vec();
    let research_rows = table_array(
        &load_toml(&repo_root.join("registry/research_narratives.toml"))?,
        "document",
    )
    .to_vec();
    let external_rows = table_array(
        &load_toml(&repo_root.join("registry/external_sources.toml"))?,
        "document",
    )
    .to_vec();
    let artifact_rows = table_array(
        &load_toml(&repo_root.join("registry/data_artifact_narratives.toml"))?,
        "document",
    )
    .to_vec();
    let legacy_lacunae = if repo_root.join(&args.lacunae_out).exists() {
        table_array(&load_toml(&repo_root.join(&args.lacunae_out))?, "lacuna").to_vec()
    } else {
        Vec::new()
    };

    let (conflict_rows, conflict_meta) = build_conflict_markers(
        &claims_rows,
        &docs_root_rows,
        &research_rows,
        &external_rows,
        &artifact_rows,
    )?;
    let (lacunae_rows, lacunae_meta) = build_lacunae(
        &claims_rows,
        &conflict_rows,
        &insights_rows,
        &experiments_rows,
        &legacy_lacunae,
    )?;

    write_ascii(
        &repo_root.join(&args.conflict_out),
        &render_conflict_markers(&conflict_rows, &conflict_meta),
    )?;
    write_ascii(
        &repo_root.join(&args.lacunae_out),
        &render_lacunae(&lacunae_rows, &lacunae_meta),
    )?;

    println!(
        "Wrote registry-integrity registry lane artifacts (canonical registry-integrity tool): conflict_markers={} lacunae={}",
        conflict_rows.len(),
        lacunae_rows.len()
    );
    Ok(())
}

/// Checks the facts a regeneration cannot repair. Marker claim references
/// come from narrative prose, and `legacy_manual` lacunae carry their
/// priority, claim references, related marker ids, title and description
/// forward verbatim, so a dangling claim or marker id, an unknown priority or
/// a blank text survives `registry-integrity` and fails here. Counts, ids,
/// enums and spans that the generator assigns itself are not re-checked.
fn verify_integrity_resolution(repo_root: &Path, args: &Args) -> Result<()> {
    let conflict_path = repo_root.join(&args.conflict_out);
    let lacunae_path = repo_root.join(&args.lacunae_out);
    let claims = table_array(
        &load_control_plane_registry(
            repo_root,
            &args.db,
            ControlPlaneCompatKind::Claims,
            "registry/claims.toml",
        )?,
        "claim",
    )
    .to_vec();
    let conflict_raw = load_toml(&conflict_path)?;
    let lacunae_raw = load_toml(&lacunae_path)?;
    let claim_ids = claims
        .iter()
        .map(|row| table_str(row, "id").to_string())
        .collect::<BTreeSet<_>>();
    let markers = table_array(&conflict_raw, "marker");
    let lacunae = table_array(&lacunae_raw, "lacuna");
    let marker_ids = markers
        .iter()
        .map(|row| table_str(row, "id").to_string())
        .collect::<BTreeSet<_>>();

    let mut failures = Vec::new();
    for row in markers {
        let marker_id = table_str(row, "id");
        for claim_ref in string_list(row, "claim_refs") {
            if !claim_ids.contains(&claim_ref) {
                failures.push(format!(
                    "marker references unknown claim id: {marker_id} -> {claim_ref}"
                ));
            }
        }
    }
    for row in lacunae {
        let lacuna_id = table_str(row, "id");
        let priority = table_str(row, "priority");
        if !["high", "medium", "low"].contains(&priority) {
            failures.push(format!(
                "invalid lacuna priority: {lacuna_id} -> {priority}"
            ));
        }
        for claim_ref in string_list(row, "claim_refs") {
            if !claim_ids.contains(&claim_ref) {
                failures.push(format!(
                    "lacuna references unknown claim id: {lacuna_id} -> {claim_ref}"
                ));
            }
        }
        for marker_id in string_list(row, "related_marker_ids") {
            if !marker_ids.contains(&marker_id) {
                failures.push(format!(
                    "lacuna references unknown conflict marker id: {lacuna_id} -> {marker_id}"
                ));
            }
        }
        if table_str(row, "title").trim().is_empty() {
            failures.push(format!("lacuna missing title: {lacuna_id}"));
        }
        if table_str(row, "description").trim().is_empty() {
            failures.push(format!("lacuna missing description: {lacuna_id}"));
        }
    }

    if !failures.is_empty() {
        println!(
            "ERROR: registry-integrity registry lane verification failed (canonical registry-integrity tool)."
        );
        for item in failures.iter().take(250) {
            println!("- {}", item);
        }
        if failures.len() > 250 {
            println!("- ... and {} more failures", failures.len() - 250);
        }
        std::process::exit(1);
    }

    println!(
        "OK: registry-integrity registry lane verified (canonical registry-integrity tool). markers={} lacunae={}",
        markers.len(),
        lacunae.len()
    );
    Ok(())
}

fn build_conflict_markers(
    claims_rows: &[Value],
    docs_root_rows: &[Value],
    research_rows: &[Value],
    external_rows: &[Value],
    artifact_rows: &[Value],
) -> Result<(Vec<ConflictMarker>, ConflictMeta)> {
    let mut markers = Vec::new();
    let mut seq = 0usize;

    let mut claim_by_id = BTreeMap::<String, (String, String, String)>::new();
    let mut statement_tokens = BTreeMap::<String, BTreeSet<String>>::new();
    for row in claims_rows {
        let claim_id = collapse(table_str(row, "id"));
        if claim_id.is_empty() {
            continue;
        }
        let status_token = status_token(table_str(row, "status"));
        let statement = collapse(table_str(row, "statement"));
        let source_content_sha256 = sha256_hex(table_str(row, "statement").as_bytes());
        claim_by_id.insert(
            claim_id.clone(),
            (
                statement.clone(),
                status_token.clone(),
                source_content_sha256.clone(),
            ),
        );
        statement_tokens.insert(claim_id.clone(), token_set(&statement)?);
        let lower = statement.to_lowercase();
        let has_positive = POSITIVE_TERMS.iter().any(|term| lower.contains(term));
        let has_negative = NEGATIVE_TERMS.iter().any(|term| lower.contains(term));
        if REFUTED_STATUS_TOKENS.contains(&status_token.as_str()) && has_positive {
            seq += 1;
            markers.push(ConflictMarker {
                id: format!("CM-{:04}", seq),
                marker_kind: "claim_status_statement_tension".to_string(),
                severity: "high".to_string(),
                status: "open".to_string(),
                claim_refs: vec![claim_id.clone()],
                source_registry: "registry/claims.toml".to_string(),
                source_document: claim_id.clone(),
                section_label: "statement".to_string(),
                line_start: 0,
                line_end: 0,
                positive_evidence: vec![statement.clone()],
                negative_evidence: vec![status_token.clone()],
                source_content_sha256: source_content_sha256.clone(),
                jaccard_overlap: 0.0,
                notes: "Refuted/negative status conflicts with positive language in statement."
                    .to_string(),
            });
        }
        if VERIFIED_STATUS_TOKENS.contains(&status_token.as_str()) && has_negative {
            seq += 1;
            markers.push(ConflictMarker {
                id: format!("CM-{:04}", seq),
                marker_kind: "claim_status_statement_tension".to_string(),
                severity: "high".to_string(),
                status: "open".to_string(),
                claim_refs: vec![claim_id.clone()],
                source_registry: "registry/claims.toml".to_string(),
                source_document: claim_id.clone(),
                section_label: "statement".to_string(),
                line_start: 0,
                line_end: 0,
                positive_evidence: vec![status_token.clone()],
                negative_evidence: vec![statement.clone()],
                source_content_sha256,
                jaccard_overlap: 0.0,
                notes: "Verified status conflicts with negative language in statement.".to_string(),
            });
        }
    }

    let claim_ids = claim_by_id.keys().cloned().collect::<Vec<_>>();
    for (idx, a_id) in claim_ids.iter().enumerate() {
        let Some((a_statement, a_status, a_content_sha256)) = claim_by_id.get(a_id).cloned() else {
            continue;
        };
        if !VERIFIED_STATUS_TOKENS.contains(&a_status.as_str())
            && !REFUTED_STATUS_TOKENS.contains(&a_status.as_str())
        {
            continue;
        }
        for b_id in claim_ids.iter().skip(idx + 1) {
            let Some((b_statement, b_status, b_content_sha256)) = claim_by_id.get(b_id).cloned()
            else {
                continue;
            };
            if !VERIFIED_STATUS_TOKENS.contains(&b_status.as_str())
                && !REFUTED_STATUS_TOKENS.contains(&b_status.as_str())
            {
                continue;
            }
            let opposite = (VERIFIED_STATUS_TOKENS.contains(&a_status.as_str())
                && REFUTED_STATUS_TOKENS.contains(&b_status.as_str()))
                || (REFUTED_STATUS_TOKENS.contains(&a_status.as_str())
                    && VERIFIED_STATUS_TOKENS.contains(&b_status.as_str()));
            if !opposite {
                continue;
            }
            let score = jaccard(
                statement_tokens.get(a_id).cloned().unwrap_or_default(),
                statement_tokens.get(b_id).cloned().unwrap_or_default(),
            );
            if score < 0.70 {
                continue;
            }
            seq += 1;
            markers.push(ConflictMarker {
                id: format!("CM-{:04}", seq),
                marker_kind: "claim_semantic_status_conflict".to_string(),
                severity: "medium".to_string(),
                status: "open".to_string(),
                claim_refs: vec![a_id.clone(), b_id.clone()],
                source_registry: "registry/claims.toml".to_string(),
                source_document: format!("{}|{}", a_id, b_id),
                section_label: "cross_claim_statement".to_string(),
                line_start: 0,
                line_end: 0,
                positive_evidence: vec![
                    format!("{}: {}", a_id, a_statement),
                    format!("{}: {}", b_id, b_statement),
                ],
                negative_evidence: vec![
                    format!("{}: {}", a_id, a_status),
                    format!("{}: {}", b_id, b_status),
                ],
                source_content_sha256: sha256_hex(
                    serde_json::to_string(&[&a_content_sha256, &b_content_sha256])?.as_bytes(),
                ),
                jaccard_overlap: (score * 1_000_000.0).round() / 1_000_000.0,
                notes: "Semantically similar claims have opposite truth-status categories."
                    .to_string(),
            });
        }
    }

    let corpora = [
        ("registry/docs_root_narratives.toml", docs_root_rows),
        ("registry/research_narratives.toml", research_rows),
        ("registry/external_sources.toml", external_rows),
        ("registry/data_artifact_narratives.toml", artifact_rows),
    ];
    for (source_registry, rows) in corpora {
        for row in rows {
            let body = table_str(row, "body_markdown");
            if body.trim().is_empty() {
                continue;
            }
            let source_markdown = collapse(table_str(row, "source_markdown"));
            let source_uid = collapse(table_str(row, "id"));
            for section in split_sections(body)? {
                let text = collapse(&section.body);
                if text.is_empty() {
                    continue;
                }
                let lower = text.to_lowercase();
                let pos_hits = POSITIVE_TERMS
                    .iter()
                    .filter(|term| lower.contains(**term))
                    .map(|s| (*s).to_string())
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                let neg_hits = NEGATIVE_TERMS
                    .iter()
                    .filter(|term| lower.contains(**term))
                    .map(|s| (*s).to_string())
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                if pos_hits.is_empty() || neg_hits.is_empty() {
                    continue;
                }
                seq += 1;
                markers.push(ConflictMarker {
                    id: format!("CM-{:04}", seq),
                    marker_kind: "section_polarity_conflict".to_string(),
                    severity: "medium".to_string(),
                    status: "open".to_string(),
                    claim_refs: extract_claim_refs(&text)?,
                    source_registry: source_registry.to_string(),
                    source_document: if source_markdown.is_empty() {
                        source_uid.clone()
                    } else {
                        source_markdown.clone()
                    },
                    section_label: section.title.clone(),
                    line_start: section.line_start,
                    line_end: section.line_end,
                    positive_evidence: pos_hits,
                    negative_evidence: neg_hits,
                    source_content_sha256: sha256_hex(section.body.as_bytes()),
                    jaccard_overlap: 0.0,
                    notes: "Section contains both positive and negative validation language."
                        .to_string(),
                });
            }
        }
    }

    markers.sort_by(|a, b| a.id.cmp(&b.id));
    let mut kind_counts = BTreeSet::new();
    let mut meta = ConflictMeta::default();
    for marker in &markers {
        kind_counts.insert(marker.marker_kind.clone());
        match marker.severity.as_str() {
            "high" => meta.high_severity_count += 1,
            "medium" => meta.medium_severity_count += 1,
            "low" => meta.low_severity_count += 1,
            _ => {}
        }
    }
    meta.marker_count = markers.len();
    meta.kind_count = kind_counts.len();
    Ok((markers, meta))
}

// Marker sequence numbers and line offsets locate one scan. Resolution belongs
// to the source, conflict kind and evidence, including the complete section
// text when polarity hits alone cannot distinguish two contradictory passages.
fn conflict_lacuna_id(marker: &ConflictMarker) -> String {
    // Ordered field pairs keep the hash independent of JSON map feature flags.
    let identity = serde_json::json!([
        ["version", 1],
        ["marker_kind", marker.marker_kind],
        [
            "claim_refs",
            marker.claim_refs.iter().collect::<BTreeSet<_>>()
        ],
        ["source_registry", marker.source_registry],
        ["source_document", marker.source_document],
        ["section_label", marker.section_label],
        ["source_content_sha256", marker.source_content_sha256],
        [
            "positive_evidence",
            marker.positive_evidence.iter().collect::<BTreeSet<_>>()
        ],
        [
            "negative_evidence",
            marker.negative_evidence.iter().collect::<BTreeSet<_>>()
        ],
    ]);
    format!("L-CM-v1-{}", sha256_hex(identity.to_string().as_bytes()))
}

fn build_lacunae(
    claims_rows: &[Value],
    conflict_markers: &[ConflictMarker],
    insights_rows: &[Value],
    experiments_rows: &[Value],
    legacy_lacunae: &[Value],
) -> Result<(Vec<Lacuna>, LacunaMeta)> {
    let mut rows = Vec::new();
    let mut seen_ids = BTreeSet::new();
    let mut live_conflicts = BTreeMap::<String, Vec<&ConflictMarker>>::new();
    for marker in conflict_markers {
        live_conflicts
            .entry(conflict_lacuna_id(marker))
            .or_default()
            .push(marker);
    }

    // Claim-status lacunae follow live status and are regenerated. Retained
    // conflict resolutions receive an active marker link only when the source
    // and evidence identity matches; unmatched records retain their history.
    for row in legacy_lacunae {
        let lacuna_id = collapse(table_str(row, "id"));
        if lacuna_id.is_empty() {
            continue;
        }
        let legacy_origin = collapse(table_str(row, "origin"));
        let legacy_title = collapse(table_str(row, "title"));
        if legacy_origin == "claims_status_scan"
            || legacy_title.starts_with(CLAIM_STATUS_LACUNA_TITLE_PREFIX)
        {
            continue;
        }
        if !seen_ids.insert(lacuna_id.clone()) {
            bail!(
                "retained lacuna id {lacuna_id} appears twice in the lacunae registry; \
                 rename or merge one record before regenerating"
            );
        }
        let conflict_derived = legacy_origin == "conflict_marker_scan"
            || legacy_origin == "conflict_marker_history"
            || lacuna_id.starts_with("L-CM-")
            || legacy_title.starts_with("Resolve conflict marker ");
        let mut related_marker_ids = string_list(row, "related_marker_ids");
        let mut historical_marker_ids = string_list(row, "historical_marker_ids");
        let origin = if conflict_derived {
            let live_markers = live_conflicts.get(&lacuna_id);
            let live_ids: Vec<String> = live_markers
                .map(|markers| markers.iter().map(|marker| marker.id.clone()).collect())
                .unwrap_or_default();
            historical_marker_ids.extend(
                related_marker_ids
                    .iter()
                    .filter(|marker_id| !live_ids.contains(marker_id))
                    .cloned(),
            );
            related_marker_ids = live_ids;
            if live_markers.is_some() {
                "conflict_marker_scan".to_string()
            } else {
                "conflict_marker_history".to_string()
            }
        } else if legacy_origin.is_empty() {
            "legacy_manual".to_string()
        } else {
            legacy_origin
        };
        historical_marker_ids.sort();
        historical_marker_ids.dedup();
        rows.push(Lacuna {
            id: lacuna_id,
            origin,
            area: {
                let area = collapse(table_str(row, "area"));
                if area.is_empty() {
                    "general".to_string()
                } else {
                    area
                }
            },
            title: collapse(table_str(row, "title")),
            description: collapse(table_str(row, "description")),
            priority: {
                let priority = collapse(table_str(row, "priority"));
                if priority.is_empty() {
                    "medium".to_string()
                } else {
                    priority
                }
            },
            status: {
                let status = collapse(table_str(row, "status"));
                if status.is_empty() {
                    "open".to_string()
                } else {
                    status
                }
            },
            claim_refs: if value_is_array(row, "claim_refs") {
                string_list(row, "claim_refs")
            } else {
                extract_claim_refs(table_str(row, "description"))?
            },
            source_refs: string_list(row, "source_refs"),
            related_marker_ids,
            historical_marker_ids,
        });
    }

    for row in claims_rows {
        let claim_id = collapse(table_str(row, "id"));
        let status = status_token(table_str(row, "status"));
        if !UNRESOLVED_STATUS_TOKENS.contains(&status.as_str()) {
            continue;
        }
        let lacuna_id = if let Some(stripped) = claim_id.strip_prefix("C-") {
            format!("L-{}", stripped)
        } else {
            format!("L-AUTO-{:04}", rows.len() + 1)
        };
        if !seen_ids.insert(lacuna_id.clone()) {
            bail!(
                "claim-status lacuna id {lacuna_id} collides with a retained non-derived lacuna; \
                 rename the retained record before regenerating the claims-status projection"
            );
        }
        let statement = collapse(table_str(row, "statement"));
        rows.push(Lacuna {
            id: lacuna_id,
            origin: "claims_status_scan".to_string(),
            area: "claims".to_string(),
            title: format!("{}{}", CLAIM_STATUS_LACUNA_TITLE_PREFIX, claim_id),
            description: format!(
                "{} remains unresolved with status token {}: {}",
                claim_id, status, statement
            ),
            priority: if ["INCONCLUSIVE", "PARTIAL"].contains(&status.as_str()) {
                "high".to_string()
            } else {
                "medium".to_string()
            },
            status: "open".to_string(),
            claim_refs: vec![claim_id],
            source_refs: vec!["registry/claims.toml".to_string()],
            related_marker_ids: Vec::new(),
            historical_marker_ids: Vec::new(),
        });
    }

    for (lacuna_id, markers) in live_conflicts {
        if !seen_ids.insert(lacuna_id.clone()) {
            continue;
        }
        let marker = markers[0];
        rows.push(Lacuna {
            id: lacuna_id,
            origin: "conflict_marker_scan".to_string(),
            area: "consistency".to_string(),
            title: format!(
                "Resolve {} in {}",
                marker.marker_kind, marker.source_document
            ),
            description: if marker.notes.is_empty() {
                "Unresolved contradiction marker.".to_string()
            } else {
                marker.notes.clone()
            },
            priority: if marker.severity == "high" {
                "high".to_string()
            } else {
                "medium".to_string()
            },
            status: "open".to_string(),
            claim_refs: marker.claim_refs.clone(),
            source_refs: vec![
                marker.source_registry.clone(),
                marker.source_document.clone(),
            ],
            related_marker_ids: markers.iter().map(|marker| marker.id.clone()).collect(),
            historical_marker_ids: Vec::new(),
        });
    }

    let claim_ids = claims_rows
        .iter()
        .map(|row| table_str(row, "id").to_string())
        .collect::<BTreeSet<_>>();
    let mut dangling = 0usize;
    for (source_name, source_rows, claims_key) in [
        ("insights", insights_rows, "claims"),
        ("experiments", experiments_rows, "claims"),
    ] {
        for row in source_rows {
            let source_id = collapse(table_str(row, "id"));
            let refs = string_list(row, claims_key);
            let missing = refs
                .into_iter()
                .filter(|claim_ref| !claim_ids.contains(claim_ref))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            if missing.is_empty() {
                continue;
            }
            dangling += 1;
            let lacuna_id = format!(
                "L-DANGLING-{}-{:03}",
                source_name[..1].to_uppercase(),
                dangling
            );
            if !seen_ids.insert(lacuna_id.clone()) {
                continue;
            }
            rows.push(Lacuna {
                id: lacuna_id,
                origin: "crossref_scan".to_string(),
                area: source_name.to_string(),
                title: format!(
                    "Dangling claim references in {} entry {}",
                    source_name, source_id
                ),
                description: format!(
                    "Entry {} references unknown claims: {}",
                    source_id,
                    missing.join(", ")
                ),
                priority: "high".to_string(),
                status: "open".to_string(),
                claim_refs: Vec::new(),
                source_refs: vec![format!("registry/{}.toml", source_name)],
                related_marker_ids: Vec::new(),
                historical_marker_ids: Vec::new(),
            });
        }
    }

    rows.sort_by(|a, b| a.id.cmp(&b.id));
    let mut origin_kinds = BTreeSet::new();
    let mut meta = LacunaMeta::default();
    for row in &rows {
        origin_kinds.insert(row.origin.clone());
        if row.status == "open" {
            meta.open_count += 1;
        }
        match row.priority.as_str() {
            "high" => meta.high_priority_count += 1,
            "medium" => meta.medium_priority_count += 1,
            "low" => meta.low_priority_count += 1,
            _ => {}
        }
    }
    meta.lacuna_count = rows.len();
    meta.origin_kind_count = origin_kinds.len();
    Ok((rows, meta))
}

fn render_conflict_markers(rows: &[ConflictMarker], meta: &ConflictMeta) -> String {
    let mut lines = vec![
        "# Conflict marker registry (registry-integrity lane strict schema; legacy batch3 compatibility).".to_string(),
        "# Generated by crates/gororoba_cli_governance/src/bin/registry_integrity.rs.".to_string(),
        "".to_string(),
        "[conflict_markers]".to_string(),
        "updated = \"deterministic\"".to_string(),
        "authoritative = true".to_string(),
        format!("marker_count = {}", meta.marker_count),
        format!("high_severity_count = {}", meta.high_severity_count),
        format!("medium_severity_count = {}", meta.medium_severity_count),
        format!("low_severity_count = {}", meta.low_severity_count),
        format!("kind_count = {}", meta.kind_count),
        "".to_string(),
    ];
    for row in rows {
        lines.extend([
            "[[marker]]".to_string(),
            format!("id = {}", esc(&row.id)),
            format!("marker_kind = {}", esc(&row.marker_kind)),
            format!("severity = {}", esc(&row.severity)),
            format!("status = {}", esc(&row.status)),
            format!("claim_refs = {}", render_list(&row.claim_refs)),
            format!("source_registry = {}", esc(&row.source_registry)),
            format!("source_document = {}", esc(&row.source_document)),
            format!("section_label = {}", esc(&row.section_label)),
            format!("line_start = {}", row.line_start),
            format!("line_end = {}", row.line_end),
            format!(
                "positive_evidence = {}",
                render_list(&row.positive_evidence)
            ),
            format!(
                "negative_evidence = {}",
                render_list(&row.negative_evidence)
            ),
            format!(
                "source_content_sha256 = {}",
                esc(&row.source_content_sha256)
            ),
            format!("jaccard_overlap = {:.6}", row.jaccard_overlap),
            format!("notes = {}", esc(&row.notes)),
            "".to_string(),
        ]);
    }
    lines.join("\n")
}

fn render_lacunae(rows: &[Lacuna], meta: &LacunaMeta) -> String {
    let mut lines = vec![
        "# Lacunae registry (registry-integrity lane strict schema; legacy batch3 compatibility)."
            .to_string(),
        "# Generated by crates/gororoba_cli_governance/src/bin/registry_integrity.rs.".to_string(),
        "".to_string(),
        "[lacunae]".to_string(),
        "updated = \"deterministic\"".to_string(),
        "authoritative = true".to_string(),
        "status = \"active\"".to_string(),
        format!("lacuna_count = {}", meta.lacuna_count),
        format!("open_count = {}", meta.open_count),
        format!("high_priority_count = {}", meta.high_priority_count),
        format!("medium_priority_count = {}", meta.medium_priority_count),
        format!("low_priority_count = {}", meta.low_priority_count),
        format!("origin_kind_count = {}", meta.origin_kind_count),
        "".to_string(),
    ];
    for row in rows {
        lines.extend([
            "[[lacuna]]".to_string(),
            format!("id = {}", esc(&row.id)),
            format!("origin = {}", esc(&row.origin)),
            format!("area = {}", esc(&row.area)),
            format!("title = {}", esc(&row.title)),
            format!("description = {}", esc(&row.description)),
            format!("priority = {}", esc(&row.priority)),
            format!("status = {}", esc(&row.status)),
            format!("claim_refs = {}", render_list(&row.claim_refs)),
            format!("source_refs = {}", render_list(&row.source_refs)),
            format!(
                "related_marker_ids = {}",
                render_list(&row.related_marker_ids)
            ),
        ]);
        if !row.historical_marker_ids.is_empty() {
            lines.push(format!(
                "historical_marker_ids = {}",
                render_list(&row.historical_marker_ids)
            ));
        }
        lines.push(String::new());
    }
    lines.join("\n")
}

fn status_token(status: &str) -> String {
    let mut token = collapse(status).to_uppercase();
    token = token.replace(['/', '-', ' '], "_");
    let cleaned = token
        .chars()
        .filter(|ch| ch.is_ascii_alphanumeric() || *ch == '_')
        .collect::<String>();
    let squashed = cleaned
        .split('_')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join("_");
    if squashed.is_empty() {
        "UNSPECIFIED".to_string()
    } else {
        squashed
    }
}

fn extract_claim_refs(text: &str) -> Result<Vec<String>> {
    let claim_re = Regex::new(r"\bC-\d{3,}\b")?;
    Ok(sorted_unique_regex(text, &claim_re))
}

fn token_set(text: &str) -> Result<BTreeSet<String>> {
    let word_re = Regex::new(r"\b[A-Za-z][A-Za-z0-9_]{2,}\b")?;
    Ok(word_re
        .find_iter(&ascii_clean(text))
        .map(|m| m.as_str().to_lowercase())
        .filter(|token| token.len() >= 4 && !STOPWORDS.contains(&token.as_str()))
        .collect())
}

fn jaccard(a: BTreeSet<String>, b: BTreeSet<String>) -> f64 {
    if a.is_empty() && b.is_empty() {
        return 0.0;
    }
    let inter = a.intersection(&b).count();
    let union = a.union(&b).count();
    if union == 0 {
        0.0
    } else {
        inter as f64 / union as f64
    }
}

#[derive(Debug, Clone)]
struct Section {
    title: String,
    line_start: i64,
    line_end: i64,
    body: String,
}

fn split_sections(text: &str) -> Result<Vec<Section>> {
    let heading_re = Regex::new(r"^(#{1,6})\s+(.+?)\s*$")?;
    let lines = ascii_clean(text)
        .lines()
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let mut sections = Vec::new();
    let mut current_title = "(root)".to_string();
    let mut current_start = 1i64;
    let mut current_lines = Vec::new();
    for (idx, line) in lines.iter().enumerate() {
        let line_no = idx as i64 + 1;
        if let Some(caps) = heading_re.captures(line) {
            sections.push(Section {
                title: current_title,
                line_start: current_start,
                line_end: current_start.max(line_no - 1),
                body: current_lines.join("\n"),
            });
            current_title = collapse(caps.get(2).map(|m| m.as_str()).unwrap_or_default());
            current_start = line_no;
            current_lines.clear();
            continue;
        }
        current_lines.push(line.clone());
    }
    sections.push(Section {
        title: current_title,
        line_start: current_start,
        line_end: current_start.max(lines.len() as i64),
        body: current_lines.join("\n"),
    });
    Ok(sections)
}

fn load_toml(path: &Path) -> Result<Value> {
    let text = fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    toml::from_str(&text).with_context(|| format!("parse TOML {}", path.display()))
}

fn load_control_plane_registry(
    repo_root: &Path,
    db_rel_path: &Path,
    kind: ControlPlaneCompatKind,
    registry_label: &str,
) -> Result<Value> {
    let db_path = repo_root.join(db_rel_path);
    let mut store = ProvenanceStore::open_read_only(&db_path)
        .with_context(|| format!("open canonical control plane {}", db_path.display()))?;
    let text = store
        .control_plane_compat_text(kind)
        .with_context(|| format!("render {registry_label} from canonical control plane"))?;
    toml::from_str(&text)
        .with_context(|| format!("parse canonical {registry_label} compatibility rendering"))
}

fn table_array<'a>(value: &'a Value, key: &str) -> &'a [Value] {
    value
        .get(key)
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .unwrap_or(&[])
}

fn table_str<'a>(value: &'a Value, key: &str) -> &'a str {
    value.get(key).and_then(Value::as_str).unwrap_or("")
}

fn string_list(value: &Value, key: &str) -> Vec<String> {
    value
        .get(key)
        .and_then(Value::as_array)
        .map(|items| {
            items
                .iter()
                .filter_map(Value::as_str)
                .map(ToOwned::to_owned)
                .collect()
        })
        .unwrap_or_default()
}

fn value_is_array(value: &Value, key: &str) -> bool {
    value.get(key).and_then(Value::as_array).is_some()
}

fn write_ascii(path: &Path, text: &str) -> Result<()> {
    assert_ascii(text, &path.display().to_string())?;
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("mkdir {}", parent.display()))?;
    }
    fs::write(path, text).with_context(|| format!("write {}", path.display()))
}

fn assert_ascii(text: &str, context: &str) -> Result<()> {
    let bad: BTreeSet<char> = text.chars().filter(|ch| (*ch as u32) > 127).collect();
    if !bad.is_empty() {
        let sample: String = bad.iter().take(20).copied().collect();
        bail!("ERROR: Non-ASCII output in {context}: {:?}", sample);
    }
    Ok(())
}

fn ascii_clean(text: &str) -> String {
    let mut out = String::new();
    for ch in text.chars() {
        if ch == '\n' || ch == '\r' || ch == '\t' {
            out.push(ch);
        } else if (ch as u32) < 32 {
            out.push(' ');
        } else if (ch as u32) <= 127 {
            out.push(ch);
        } else {
            out.push_str(&format!("\\u{:04X}", ch as u32));
        }
    }
    out
}

fn collapse(text: &str) -> String {
    ascii_clean(text)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn sorted_unique_regex(text: &str, regex: &Regex) -> Vec<String> {
    regex
        .find_iter(text)
        .map(|m| m.as_str().to_string())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn esc(value: &str) -> String {
    serde_json::to_string(&ascii_clean(value)).unwrap_or_else(|_| "\"\"".to_string())
}

fn render_list(values: &[String]) -> String {
    if values.is_empty() {
        "[]".to_string()
    } else {
        format!(
            "[{}]",
            values
                .iter()
                .map(|item| esc(item))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table_rows(document: &str, key: &str) -> Vec<Value> {
        toml::from_str::<Value>(document)
            .expect("test TOML must parse")
            .get(key)
            .and_then(Value::as_array)
            .expect("test TOML must contain the requested array")
            .clone()
    }

    fn verified_claim(claim_id: &str, statement: &str) -> Value {
        Value::Table(
            [
                ("id", claim_id),
                ("status", "Verified"),
                ("statement", statement),
            ]
            .into_iter()
            .map(|(key, value)| (key.to_string(), Value::String(value.to_string())))
            .collect(),
        )
    }

    fn conflict_rows(claims: &[Value]) -> Vec<ConflictMarker> {
        build_conflict_markers(claims, &[], &[], &[], &[])
            .expect("build fixture conflict markers")
            .0
    }

    #[test]
    fn conflict_resolution_follows_semantic_identity_across_insertion_and_reordering() {
        let original_claims = [
            verified_claim("C-002", "An obstruction bounds the first construction."),
            verified_claim("C-003", "The second construction fails its boundary test."),
        ];
        let original_markers = conflict_rows(&original_claims);
        let resolved_id = conflict_lacuna_id(&original_markers[0]);
        let (mut retained, meta) =
            build_lacunae(&original_claims, &original_markers, &[], &[], &[]).unwrap();
        let resolved = retained
            .iter_mut()
            .find(|row| row.id == resolved_id)
            .unwrap();
        resolved.status = "resolved".to_string();
        resolved.description = "The boundary obstruction is the proved result.".to_string();
        resolved.source_refs.push("proofs/boundary.v".to_string());
        let original_text = render_lacunae(&retained, &meta);
        let inserted_claims = [
            verified_claim(
                "C-001",
                "The new candidate fails the associativity identity.",
            ),
            original_claims[1].clone(),
            original_claims[0].clone(),
        ];
        let inserted_markers = conflict_rows(&inserted_claims);
        let (inserted, inserted_meta) = build_lacunae(
            &inserted_claims,
            &inserted_markers,
            &[],
            &[],
            &table_rows(&original_text, "lacuna"),
        )
        .unwrap();
        assert_eq!(inserted.len(), 3);
        assert_eq!(inserted_meta.open_count, 2);
        let new_conflict = inserted
            .iter()
            .find(|row| row.claim_refs == ["C-001"])
            .unwrap();
        assert_eq!(new_conflict.status, "open");
        assert_ne!(new_conflict.id, resolved_id);
        assert_eq!(new_conflict.related_marker_ids, ["CM-0001"]);
        let resolved = inserted.iter().find(|row| row.id == resolved_id).unwrap();
        assert_eq!(resolved.claim_refs, ["C-002"]);
        assert_eq!(resolved.status, "resolved");
        assert_eq!(resolved.related_marker_ids, ["CM-0003"]);
        assert_eq!(resolved.historical_marker_ids, ["CM-0001"]);
        assert!(
            resolved
                .source_refs
                .iter()
                .any(|source| source == "proofs/boundary.v")
        );
        assert_eq!(
            resolved.description,
            "The boundary obstruction is the proved result."
        );

        let reordered_claims = [
            inserted_claims[2].clone(),
            inserted_claims[0].clone(),
            inserted_claims[1].clone(),
        ];
        let reordered_markers = conflict_rows(&reordered_claims);
        let (reordered, _) = build_lacunae(
            &reordered_claims,
            &reordered_markers,
            &[],
            &[],
            &table_rows(&render_lacunae(&inserted, &inserted_meta), "lacuna"),
        )
        .unwrap();
        assert_eq!(reordered.len(), 3);
        assert_eq!(
            reordered
                .iter()
                .find(|row| row.id == resolved_id)
                .unwrap()
                .status,
            "resolved"
        );
        assert_eq!(
            reordered
                .iter()
                .find(|row| row.claim_refs == ["C-001"])
                .unwrap()
                .status,
            "open"
        );
    }

    #[test]
    fn unbound_conflict_resolution_remains_history_without_suppressing_live_marker() {
        let claims = [verified_claim(
            "C-1310",
            "The candidate fails its associativity identity.",
        )];
        let markers = conflict_rows(&claims);
        let legacy_lacunae = table_rows(
            r#"
[[lacuna]]
id = "L-CM-0001"
origin = "legacy_manual"
title = "Resolve conflict marker CM-0001"
description = "Retained resolution evidence for a different claim."
status = "resolved"
claim_refs = ["C-007"]
source_refs = ["proofs/retained.v"]
related_marker_ids = ["CM-0001"]
"#,
            "lacuna",
        );
        let (rows, meta) = build_lacunae(&claims, &markers, &[], &[], &legacy_lacunae).unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(meta.open_count, 1);
        let historical = rows.iter().find(|row| row.id == "L-CM-0001").unwrap();
        assert_eq!(historical.status, "resolved");
        assert_eq!(historical.origin, "conflict_marker_history");
        assert_eq!(historical.claim_refs, ["C-007"]);
        assert_eq!(historical.source_refs, ["proofs/retained.v"]);
        assert!(historical.related_marker_ids.is_empty());
        assert_eq!(historical.historical_marker_ids, ["CM-0001"]);
        let live = rows
            .iter()
            .find(|row| row.id == conflict_lacuna_id(&markers[0]))
            .unwrap();
        assert_eq!(live.status, "open");
        assert_eq!(live.claim_refs, ["C-1310"]);

        let text = render_lacunae(&rows, &meta);
        let (repeated, repeated_meta) =
            build_lacunae(&claims, &markers, &[], &[], &table_rows(&text, "lacuna")).unwrap();
        assert_eq!(render_lacunae(&repeated, &repeated_meta), text);
    }

    #[test]
    fn changed_section_content_reopens_conflict_even_with_identical_polarity_hits() {
        let documents = table_rows(
            r##"
[[document]]
id = "D-001"
source_markdown = "docs/fixture.md"
body_markdown = "# Result\nThe confirmed computation fails the first constraint."
"##,
            "document",
        );
        let original = build_conflict_markers(&[], &documents, &[], &[], &[])
            .unwrap()
            .0;
        assert_eq!(original.len(), 1);
        let (mut retained, meta) = build_lacunae(&[], &original, &[], &[], &[]).unwrap();
        retained[0].status = "resolved".to_string();
        let mut edited_documents = documents.clone();
        edited_documents[0]["body_markdown"] = Value::String(
            "# Result\nThe confirmed computation fails the second constraint.".to_string(),
        );
        let edited = build_conflict_markers(&[], &edited_documents, &[], &[], &[])
            .unwrap()
            .0;
        assert_eq!(original[0].positive_evidence, edited[0].positive_evidence);
        assert_eq!(original[0].negative_evidence, edited[0].negative_evidence);
        assert_ne!(
            conflict_lacuna_id(&original[0]),
            conflict_lacuna_id(&edited[0])
        );
        let (rows, _) = build_lacunae(
            &[],
            &edited,
            &[],
            &[],
            &table_rows(&render_lacunae(&retained, &meta), "lacuna"),
        )
        .unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(
            rows.iter()
                .find(|row| row.origin == "conflict_marker_scan")
                .unwrap()
                .status,
            "open"
        );
        assert_eq!(
            rows.iter()
                .find(|row| row.origin == "conflict_marker_history")
                .unwrap()
                .status,
            "resolved"
        );

        let mut relocated = edited[0].clone();
        relocated.id = "CM-9999".to_string();
        relocated.line_start += 10;
        relocated.line_end += 10;
        assert_eq!(
            conflict_lacuna_id(&relocated),
            conflict_lacuna_id(&edited[0])
        );
    }

    #[test]
    fn duplicate_conflict_sightings_share_one_stable_lacuna() {
        let claim = verified_claim("C-001", "The candidate fails its identity.");
        let claims = [claim.clone(), claim];
        let markers = conflict_rows(&claims);
        let (rows, meta) = build_lacunae(&claims, &markers, &[], &[], &[]).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].related_marker_ids, ["CM-0001", "CM-0002"]);
        let text = render_lacunae(&rows, &meta);
        let (repeated, repeated_meta) =
            build_lacunae(&claims, &markers, &[], &[], &table_rows(&text, "lacuna")).unwrap();
        assert_eq!(render_lacunae(&repeated, &repeated_meta), text);
    }

    #[test]
    fn canonical_export_preserves_integrity_history_and_generation_is_idempotent() {
        let claims = [verified_claim("C-001", "The candidate fails its identity.")];
        let (markers, marker_meta) = build_conflict_markers(&claims, &[], &[], &[], &[]).unwrap();
        let (mut rows, _) = build_lacunae(&claims, &markers, &[], &[], &[]).unwrap();
        rows[0].status = "resolved".to_string();
        rows[0].historical_marker_ids = vec!["CM-0042".to_string()];
        let (rows, meta) = build_lacunae(
            &claims,
            &markers,
            &[],
            &[],
            &table_rows(&render_lacunae(&rows, &LacunaMeta::default()), "lacuna"),
        )
        .unwrap();
        let lacunae_text = render_lacunae(&rows, &meta);
        let marker_text = render_conflict_markers(&markers, &marker_meta);
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let fixture = std::env::temp_dir().join(format!(
            "gororoba-registry-integrity-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&fixture).unwrap();
        let registry = fixture.join("registry");
        fs::create_dir(&registry).unwrap();
        let lacunae_path = registry.join("lacunae.toml");
        let marker_path = registry.join("conflict_markers.toml");
        fs::write(&lacunae_path, &lacunae_text).unwrap();
        fs::write(&marker_path, &marker_text).unwrap();
        let mut store = ProvenanceStore::open(Path::new(":memory:")).unwrap();
        for _ in 0..3 {
            assert_eq!(store.ingest_lacunae(&lacunae_text).unwrap(), 1);
            store
                .record_registry_snapshot(&fixture, "lacunae", &lacunae_path, &lacunae_text)
                .unwrap();
            store
                .record_registry_snapshot(&fixture, "conflict_markers", &marker_path, &marker_text)
                .unwrap();
            // The typed canonical exporter owns six lanes plus transitions;
            // retained integrity lanes stay in their generator-owned files.
            store
                .export_control_plane_compat_paths(
                    &fixture,
                    provenance_store::CompatExportPaths {
                        claims: &registry.join("claims.toml"),
                        insights: &registry.join("insights.toml"),
                        experiments: &registry.join("experiments.toml"),
                        binaries: &registry.join("binaries.toml"),
                        theorems: &registry.join("theorems.toml"),
                        theorems_mirror: &registry.join("theorems_mirror.toml"),
                    },
                )
                .unwrap();
            assert_eq!(fs::read_to_string(&lacunae_path).unwrap(), lacunae_text);
            assert_eq!(fs::read_to_string(&marker_path).unwrap(), marker_text);
            assert_eq!(
                store.registry_snapshot("lacunae").unwrap().unwrap(),
                lacunae_text
            );
            assert_eq!(
                store
                    .registry_snapshot("conflict_markers")
                    .unwrap()
                    .unwrap(),
                marker_text
            );
            let (regenerated, regenerated_meta) = build_lacunae(
                &claims,
                &markers,
                &[],
                &[],
                table_array(&load_toml(&lacunae_path).unwrap(), "lacuna"),
            )
            .unwrap();
            assert_eq!(
                render_lacunae(&regenerated, &regenerated_meta),
                lacunae_text
            );
        }
        for name in [
            "claims",
            "insights",
            "experiments",
            "binaries",
            "theorems",
            "theorems_mirror",
            "claim_transitions",
            "claim_relations",
            "lacunae",
            "conflict_markers",
        ] {
            fs::remove_file(registry.join(format!("{name}.toml"))).unwrap();
        }
        fs::remove_dir(&registry).unwrap();
        fs::remove_dir(&fixture).unwrap();
    }

    #[test]
    fn claim_status_projection_rejects_retained_id_collision() {
        let claims = table_rows(
            r#"
[[claim]]
id = "C-001"
status = "Partial"
statement = "Collision probe."
"#,
            "claim",
        );
        let legacy_lacunae = table_rows(
            r#"
[[lacuna]]
id = "L-001"
origin = "legacy_manual"
title = "Retained manual record"
description = "Manual evidence remains distinct."
priority = "medium"
status = "open"
"#,
            "lacuna",
        );

        let error = build_lacunae(&claims, &[], &[], &[], &legacy_lacunae)
            .expect_err("a claim-status projection must not suppress a retained lacuna");
        assert!(error.to_string().contains("collides"));
    }

    #[test]
    fn retained_lacuna_duplicate_id_fails_the_build() {
        let retained = r#"
[[lacuna]]
id = "L-002"
origin = "legacy_manual"
title = "First retained record"
description = "First text."
priority = "low"
status = "open"
"#;
        let duplicated = format!("{retained}{}", retained.replace("First", "Second"));
        let legacy_lacunae = table_rows(&duplicated, "lacuna");

        let error = build_lacunae(&[], &[], &[], &[], &legacy_lacunae)
            .expect_err("a duplicated retained id must not drop one record silently");
        assert!(error.to_string().contains("appears twice"));
    }
}
