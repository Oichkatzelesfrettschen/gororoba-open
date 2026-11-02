//! Transactional retirement of external-source dossier bodies whose bytes live in the
//! documents repositories.
//!
//! A retired dossier keeps its identity (`id`, `slug`, `title`, citation URLs and claim
//! references) and loses its repository-side Markdown: `body_markdown` and `source_markdown`
//! become empty, so `render_external_sources_compat_outputs` emits no file for it and the
//! dossier registry carries no paper text. The evidence row in `export_runs` records the
//! SHA-256, byte length and line count of each removed body and never the body text.

use crate::{
    ProvenanceStore,
    artifact_paths::{mark_dry_run_replay, sha256},
};
use anyhow::{Context, Result, bail};
use chrono::Utc;
use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeSet;

const ACTION: &str = "retire-external-source-dossier-bodies";

/// `content_kind` of a dossier whose transcription is held outside this repository.
pub const RETIRED_DOSSIER_CONTENT_KIND: &str = "custody_pointer";
/// `authority_level` of a retired dossier: the row points at a source and captures none.
pub const RETIRED_DOSSIER_AUTHORITY_LEVEL: &str = "citation_pointer";
/// `verification_level` of a retired dossier.
pub const RETIRED_DOSSIER_VERIFICATION_LEVEL: &str = "not_captured";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DossierBodyRetirementSpec {
    pub schema_version: u32,
    pub retire_key: String,
    pub actor: String,
    pub reason: String,
    /// Sentence appended to each retired dossier's `notes`; states where the bytes live.
    #[serde(default)]
    pub custody_note: String,
    #[serde(default)]
    pub retire: Vec<DossierBodyRetirement>,
    /// Index dossier whose body lists the retired dossiers' files.
    #[serde(default)]
    pub index: Option<DossierIndexPrune>,
    /// Dossiers that stay in the repository but name removed files in a body line or `path_ref`.
    #[serde(default)]
    pub edit: Vec<DossierLineEdit>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DossierBodyRetirement {
    pub id: String,
    /// Repository path the dossier must name now.
    pub expected_source_markdown: String,
    /// SHA-256 of the body the dossier must hold now.
    pub expected_body_sha256: String,
    /// Line count the dossier must record now.
    pub expected_line_count: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DossierIndexPrune {
    pub id: String,
    /// SHA-256 of the index body the dossier must hold now.
    pub expected_body_sha256: String,
    /// Body lines to drop; each must occur exactly once.
    pub remove_body_lines: Vec<String>,
    /// `path_ref` values to drop; each must be present.
    pub remove_path_refs: Vec<String>,
}

/// Replacement of one body line; an empty `to` drops the line.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DossierLineReplacement {
    pub from: String,
    #[serde(default)]
    pub to: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DossierLineEdit {
    pub id: String,
    /// SHA-256 of the body the dossier must hold now.
    pub expected_body_sha256: String,
    /// Body lines to replace or drop; each `from` must occur exactly once.
    #[serde(default)]
    pub replace_body_lines: Vec<DossierLineReplacement>,
    /// `path_ref` values to drop; each must be present.
    #[serde(default)]
    pub remove_path_refs: Vec<String>,
}

struct DossierState {
    summary: Value,
    body: String,
    source_markdown: String,
    line_count: i64,
    notes: String,
}

fn text_summary(text: &str) -> Value {
    json!({
        "sha256": sha256(text.as_bytes()),
        "bytes": text.len(),
        "lines": text.lines().count(),
    })
}

fn value_rows(connection: &Connection, id: &str) -> Result<Value> {
    let mut statement = connection.prepare(
        "SELECT relation, ord, value FROM external_source_dossier_values \
         WHERE dossier_id = ?1 ORDER BY relation, ord",
    )?;
    let rows = statement
        .query_map([id], |row| {
            Ok(json!([
                row.get::<_, String>(0)?,
                row.get::<_, i64>(1)?,
                row.get::<_, String>(2)?
            ]))
        })?
        .collect::<std::result::Result<Vec<_>, _>>()?;
    Ok(Value::Array(rows))
}

/// Row evidence that holds every column except the body text, which enters as a digest.
fn dossier_state(connection: &Connection, id: &str) -> Result<DossierState> {
    let row = connection
        .query_row(
            "SELECT source_markdown, slug, title, status_token, content_kind, authority_level, \
                    verification_level, operational_role, source_lineage_summary, \
                    has_full_transcript, line_count, notes, body_markdown \
             FROM external_source_dossiers WHERE id = ?1",
            [id],
            |row| {
                Ok((
                    [
                        row.get::<_, String>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, String>(3)?,
                        row.get::<_, String>(4)?,
                        row.get::<_, String>(5)?,
                        row.get::<_, String>(6)?,
                        row.get::<_, String>(7)?,
                        row.get::<_, String>(8)?,
                    ],
                    row.get::<_, i64>(9)?,
                    row.get::<_, i64>(10)?,
                    row.get::<_, String>(11)?,
                    row.get::<_, String>(12)?,
                ))
            },
        )
        .optional()?
        .with_context(|| format!("missing external-source dossier {id}"))?;
    let (text, has_full_transcript, line_count, notes, body) = row;
    let summary = json!({
        "id": id,
        "source_markdown": text[0],
        "slug": text[1],
        "title": text[2],
        "status_token": text[3],
        "content_kind": text[4],
        "authority_level": text[5],
        "verification_level": text[6],
        "operational_role": text[7],
        "source_lineage_summary": text[8],
        "has_full_transcript": has_full_transcript,
        "line_count": line_count,
        "notes": notes,
        "body": text_summary(&body),
        "values": value_rows(connection, id)?,
    });
    Ok(DossierState {
        summary,
        body,
        source_markdown: text[0].clone(),
        line_count,
        notes,
    })
}

fn check_digest(name: &str, digest: &str) -> Result<()> {
    if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        bail!("{name} must be a 64-digit SHA-256 hex digest");
    }
    Ok(())
}

fn validate(spec: &DossierBodyRetirementSpec) -> Result<()> {
    if spec.schema_version != 1 || (spec.retire.is_empty() && spec_edits(spec).is_empty()) {
        bail!("dossier retirement requires schema_version 1 and a retire or edit entry");
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
    if !spec.retire.is_empty() && spec.custody_note.trim().is_empty() {
        bail!("custody_note must be nonempty when dossiers are retired");
    }
    let mut ids = BTreeSet::new();
    for retirement in &spec.retire {
        if retirement.id.is_empty() || !ids.insert(&retirement.id) {
            bail!("empty or duplicate dossier ID {}", retirement.id);
        }
        if retirement.expected_source_markdown.trim().is_empty() {
            bail!(
                "expected source_markdown must be nonempty for {}",
                retirement.id
            );
        }
        check_digest("expected_body_sha256", &retirement.expected_body_sha256)?;
    }
    let mut edited = BTreeSet::new();
    for edit in spec_edits(spec) {
        if ids.contains(&edit.id) {
            bail!("edited dossier {} is also in the retire set", edit.id);
        }
        if !edited.insert(edit.id.clone()) {
            bail!(
                "dossier {} appears in more than one edit; the index prune counts as an edit, so merge them into one entry",
                edit.id
            );
        }
        check_digest("edit expected_body_sha256", &edit.expected_body_sha256)?;
        let refs: BTreeSet<_> = edit.remove_path_refs.iter().collect();
        let from: BTreeSet<_> = edit
            .replace_body_lines
            .iter()
            .map(|line| &line.from)
            .collect();
        if refs.len() != edit.remove_path_refs.len()
            || from.len() != edit.replace_body_lines.len()
            || (refs.is_empty() && from.is_empty())
            || edit
                .replace_body_lines
                .iter()
                .any(|line| line.from.is_empty())
        {
            bail!(
                "dossier edit requires distinct, nonempty edits for {}",
                edit.id
            );
        }
    }
    Ok(())
}

/// The index prune and the line edits as one list; an index prune drops each listed line.
fn spec_edits(spec: &DossierBodyRetirementSpec) -> Vec<DossierLineEdit> {
    let mut edits = Vec::new();
    if let Some(index) = &spec.index {
        edits.push(DossierLineEdit {
            id: index.id.clone(),
            expected_body_sha256: index.expected_body_sha256.clone(),
            replace_body_lines: index
                .remove_body_lines
                .iter()
                .map(|line| DossierLineReplacement {
                    from: line.clone(),
                    to: String::new(),
                })
                .collect(),
            remove_path_refs: index.remove_path_refs.clone(),
        });
    }
    edits.extend(spec.edit.iter().cloned());
    edits
}

/// Apply one line edit and return the row evidence before and after.
fn apply_line_edit(transaction: &Connection, edit: &DossierLineEdit) -> Result<(Value, Value)> {
    let state = dossier_state(transaction, &edit.id)?;
    if sha256(state.body.as_bytes()) != edit.expected_body_sha256 {
        bail!("stale expected body digest for {}", edit.id);
    }
    let mut lines: Vec<String> = state.body.split('\n').map(str::to_string).collect();
    let mut dropped = 0i64;
    for replacement in &edit.replace_body_lines {
        let hits: Vec<usize> = lines
            .iter()
            .enumerate()
            .filter(|(_, line)| **line == replacement.from)
            .map(|(position, _)| position)
            .collect();
        if hits.len() != 1 {
            bail!(
                "body line must occur exactly once in {}: {} ({} found)",
                edit.id,
                replacement.from,
                hits.len()
            );
        }
        if replacement.to.is_empty() {
            lines.remove(hits[0]);
            dropped += 1;
        } else {
            lines[hits[0]] = replacement.to.clone();
        }
    }
    let body = lines.join("\n");
    let mut paths: Vec<String> = {
        let mut statement = transaction.prepare(
            "SELECT value FROM external_source_dossier_values \
             WHERE dossier_id = ?1 AND relation = 'path_ref' ORDER BY ord",
        )?;
        statement
            .query_map([&edit.id], |row| row.get::<_, String>(0))?
            .collect::<std::result::Result<_, _>>()?
    };
    for removal in &edit.remove_path_refs {
        let Some(position) = paths.iter().position(|path| path == removal) else {
            bail!("path_ref absent from {}: {removal}", edit.id);
        };
        paths.remove(position);
    }
    transaction.execute(
        "DELETE FROM external_source_dossier_values \
         WHERE dossier_id = ?1 AND relation = 'path_ref'",
        [&edit.id],
    )?;
    for (ord, path) in paths.iter().enumerate() {
        transaction.execute(
            "INSERT INTO external_source_dossier_values (dossier_id, relation, ord, value) \
             VALUES (?1, 'path_ref', ?2, ?3)",
            params![edit.id, ord as i64, path],
        )?;
    }
    transaction.execute(
        "UPDATE external_source_dossiers \
         SET body_markdown = ?2, line_count = max(line_count - ?3, 0) WHERE id = ?1",
        params![edit.id, body, dropped],
    )?;
    let after = dossier_state(transaction, &edit.id)?;
    Ok((state.summary, after.summary))
}

fn delta_lines(before: &Value, after: &Value) -> Vec<String> {
    let id = before["id"].as_str().unwrap_or_default();
    let mut lines = Vec::new();
    for field in [
        "source_markdown",
        "content_kind",
        "authority_level",
        "verification_level",
        "has_full_transcript",
        "line_count",
        "notes",
    ] {
        if before[field] != after[field] {
            lines.push(format!(
                "{id}.{field}: {} -> {}",
                before[field], after[field]
            ));
        }
    }
    if before["body"] != after["body"] {
        lines.push(format!(
            "{id}.body_markdown: {} B, {} lines, sha256 {} -> {} B, {} lines, sha256 {}",
            before["body"]["bytes"],
            before["body"]["lines"],
            before["body"]["sha256"].as_str().unwrap_or_default(),
            after["body"]["bytes"],
            after["body"]["lines"],
            after["body"]["sha256"].as_str().unwrap_or_default()
        ));
    }
    if before["values"] != after["values"] {
        lines.push(format!(
            "{id}.external_source_dossier_values: {} -> {} rows",
            before["values"].as_array().map_or(0, Vec::len),
            after["values"].as_array().map_or(0, Vec::len)
        ));
    }
    lines
}

fn replay(transaction: &Connection, spec: &DossierBodyRetirementSpec) -> Result<Option<Value>> {
    let spec_sha256 = sha256(serde_json::to_vec(spec)?);
    let mut statement = transaction
        .prepare("SELECT details_json FROM export_runs WHERE action = ?1 ORDER BY id")?;
    let reports = statement.query_map([ACTION], |row| row.get::<_, String>(0))?;
    for report in reports {
        let report: Value = serde_json::from_str(&report?)?;
        if report["retire_key"] != spec.retire_key {
            continue;
        }
        if report["spec_sha256"] != spec_sha256 {
            bail!("retire key already records a different specification");
        }
        let retained = report["dossiers"]
            .as_array()
            .context("dossier retirement report lacks row evidence")?;
        for evidence in retained {
            let id = evidence["id"].as_str().context("evidence lacks an ID")?;
            if dossier_state(transaction, id)?.summary != evidence["after"] {
                bail!("post-retirement state drift for {id}");
            }
        }
        return Ok(Some(report));
    }
    Ok(None)
}

/// Full-text tables declared `content=<table>, content_rowid='ROWID'` over a rowid table
/// (`db/migrations/0010_knowledge_and_planning.sql`, `0011_fts5_crossrefs.sql`). They join to
/// their content table by implicit rowid, which `VACUUM` may renumber.
const ROWID_EXTERNAL_CONTENT_FTS_TABLES: [&str; 4] = [
    "claims_fts",
    "insights_fts",
    "bibliography_fts",
    "research_narrative_search",
];

/// Rewrites the store file without free pages, which hold the removed bodies after `UPDATE`,
/// and rebuilds the rowid-keyed full-text indexes in one transaction. Runs after the mutation
/// has committed, so each failure names that state.
fn compact_store(conn: &mut Connection) -> Result<()> {
    conn.execute_batch("VACUUM").context(
        "the retirement is committed, but VACUUM did not run, so the removed bodies remain in \
         free pages of the store file; close every other connection to the store and run the \
         same specification again to compact it",
    )?;
    let rebuild_failed = |table: &str| {
        format!(
            "the retirement is committed and the store is compacted, but the {table} full-text \
             index was not rebuilt; run the same specification again"
        )
    };
    let rebuild = conn.transaction()?;
    for table in ROWID_EXTERNAL_CONTENT_FTS_TABLES {
        rebuild
            .execute(
                &format!("INSERT INTO {table}({table}) VALUES('rebuild')"),
                [],
            )
            .with_context(|| rebuild_failed(table))?;
    }
    rebuild
        .commit()
        .with_context(|| rebuild_failed("external-content"))?;
    Ok(())
}

impl ProvenanceStore {
    /// Empty the bodies of the named dossiers, clear their repository Markdown path, record the
    /// custody sentence, and prune the index dossier, atomically. `dry_run` runs every step and
    /// rolls the transaction back, so the returned report is the exact row delta.
    pub fn retire_external_source_dossier_bodies(
        &mut self,
        spec: &DossierBodyRetirementSpec,
        dry_run: bool,
    ) -> Result<Value> {
        validate(spec)?;
        let spec_sha256 = sha256(serde_json::to_vec(spec)?);
        let transaction = self
            .conn
            .transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
        if let Some(mut report) = replay(&transaction, spec)? {
            // A previous run that committed and then failed to compact leaves the removed
            // bodies in free pages; replaying the specification retries the compaction.
            transaction.rollback()?;
            mark_dry_run_replay(&mut report, dry_run);
            if !dry_run {
                compact_store(&mut self.conn)?;
            }
            return Ok(report);
        }
        let mut dossiers = Vec::new();
        let mut delta = Vec::new();
        for retirement in &spec.retire {
            let state = dossier_state(&transaction, &retirement.id)?;
            if state.source_markdown != retirement.expected_source_markdown {
                bail!("stale expected source_markdown for {}", retirement.id);
            }
            if sha256(state.body.as_bytes()) != retirement.expected_body_sha256 {
                bail!("stale expected body digest for {}", retirement.id);
            }
            if state.line_count != i64::from(retirement.expected_line_count) {
                bail!("stale expected line count for {}", retirement.id);
            }
            let notes = if state.notes.trim().is_empty() {
                spec.custody_note.trim().to_string()
            } else {
                format!("{} {}", state.notes.trim_end(), spec.custody_note.trim())
            };
            transaction.execute(
                "UPDATE external_source_dossiers SET body_markdown = '', source_markdown = '', \
                 has_full_transcript = 0, line_count = 0, notes = ?2, content_kind = ?3, \
                 authority_level = ?4, verification_level = ?5 WHERE id = ?1",
                params![
                    retirement.id,
                    notes,
                    RETIRED_DOSSIER_CONTENT_KIND,
                    RETIRED_DOSSIER_AUTHORITY_LEVEL,
                    RETIRED_DOSSIER_VERIFICATION_LEVEL
                ],
            )?;
            let after = dossier_state(&transaction, &retirement.id)?;
            delta.extend(delta_lines(&state.summary, &after.summary));
            dossiers.push(
                json!({"id": retirement.id, "before": state.summary, "after": after.summary}),
            );
        }
        for edit in spec_edits(spec) {
            let (before, after) = apply_line_edit(&transaction, &edit)?;
            delta.extend(delta_lines(&before, &after));
            dossiers.push(json!({"id": edit.id, "before": before, "after": after}));
        }
        let mut report = json!({
            "schema_version": 1,
            "retire_key": spec.retire_key,
            "actor": spec.actor,
            "reason": spec.reason,
            "spec_sha256": spec_sha256,
            "spec_hash_encoding": "serde_json serialization of typed specification",
            "spec": spec,
            "dossiers": dossiers,
            "delta": delta,
        });
        if dry_run {
            report["dry_run"] = Value::Bool(true);
            transaction.rollback()?;
            return Ok(report);
        }
        transaction.execute(
            "INSERT INTO export_runs (action, created_at, artifact_count, document_count, details_json) \
             VALUES (?1, ?2, 0, ?3, ?4)",
            params![
                ACTION,
                Utc::now().to_rfc3339(),
                spec.retire.len() as i64,
                serde_json::to_string(&report)?
            ],
        )?;
        transaction.commit()?;
        compact_store(&mut self.conn)?;
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
    const MARKER: &str = "zq-unique-transcription-marker-7731";

    struct Fixture {
        directory: PathBuf,
        store: ProvenanceStore,
        spec: DossierBodyRetirementSpec,
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.directory).expect("remove test fixture");
        }
    }

    fn body(id: &str) -> String {
        format!("# {id}\n\nParagraph {MARKER} for {id}.\nSecond line.\n")
    }

    fn edited_body() -> String {
        "# XS-E\n\n- Local PDF: `data/x.pdf`\n- Kept line.\n- Cached text: `data/x.txt`\n"
            .to_string()
    }

    fn index_body() -> String {
        "# Index\n\n- `XS-A`: `docs/a.md`\n- `XS-B`: `docs/b.md`\n- `XS-C`: `docs/c.md`\n"
            .to_string()
    }

    fn fixture() -> Fixture {
        let directory = std::env::temp_dir().join(format!(
            "dossier-retire-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let store = ProvenanceStore::open(&directory.join("test.sqlite3")).unwrap();
        for (id, path, body_text, transcript) in [
            ("XS-A", "docs/a.md", body("XS-A"), 1),
            ("XS-B", "docs/b.md", body("XS-B"), 1),
            ("XS-C", "docs/c.md", body("XS-C").replace(MARKER, "kept"), 0),
            ("XS-I", "docs/index.md", index_body(), 0),
            ("XS-E", "docs/e.md", edited_body(), 0),
        ] {
            store
                .conn
                .execute(
                    "INSERT INTO external_source_dossiers VALUES (?1, ?2, ?1, 'Title', 'REFERENCE', \
                     'paper_transcript', 'primary_cached_paper', 'source_capture', 'reference_capture', \
                     '', ?3, ?4, 'Cached transcript.', ?5)",
                    params![
                        id,
                        path,
                        transcript,
                        body_text.lines().count() as i64,
                        body_text
                    ],
                )
                .unwrap();
            store
                .conn
                .execute(
                    "INSERT INTO external_source_dossier_values VALUES (?1, 'url_ref', 0, 'https://example.org/paper')",
                    [id],
                )
                .unwrap();
        }
        for (ord, path) in ["docs/a.md", "docs/b.md", "docs/c.md"].iter().enumerate() {
            store
                .conn
                .execute(
                    "INSERT INTO external_source_dossier_values VALUES ('XS-I', 'path_ref', ?1, ?2)",
                    params![ord as i64, path],
                )
                .unwrap();
        }
        for (ord, path) in ["data/x.pdf", "data/y.pdf"].iter().enumerate() {
            store
                .conn
                .execute(
                    "INSERT INTO external_source_dossier_values VALUES ('XS-E', 'path_ref', ?1, ?2)",
                    params![ord as i64, path],
                )
                .unwrap();
        }
        let spec = DossierBodyRetirementSpec {
            schema_version: 1,
            retire_key: "retire-test".into(),
            actor: "test".into(),
            reason: "bytes are held in the documents repositories".into(),
            custody_note: "The transcription is held in the documents repositories.".into(),
            retire: ["XS-A", "XS-B"]
                .iter()
                .map(|id| DossierBodyRetirement {
                    id: (*id).into(),
                    expected_source_markdown: format!("docs/{}.md", id[3..].to_lowercase()),
                    expected_body_sha256: sha256(body(id).as_bytes()),
                    expected_line_count: body(id).lines().count() as u32,
                })
                .collect(),
            index: Some(DossierIndexPrune {
                id: "XS-I".into(),
                expected_body_sha256: sha256(index_body().as_bytes()),
                remove_body_lines: vec![
                    "- `XS-A`: `docs/a.md`".into(),
                    "- `XS-B`: `docs/b.md`".into(),
                ],
                remove_path_refs: vec!["docs/a.md".into(), "docs/b.md".into()],
            }),
            edit: vec![DossierLineEdit {
                id: "XS-E".into(),
                expected_body_sha256: sha256(edited_body().as_bytes()),
                replace_body_lines: vec![
                    DossierLineReplacement {
                        from: "- Local PDF: `data/x.pdf`".into(),
                        to: "- Local PDF: held in the documents repositories.".into(),
                    },
                    DossierLineReplacement {
                        from: "- Cached text: `data/x.txt`".into(),
                        to: String::new(),
                    },
                ],
                remove_path_refs: vec!["data/x.pdf".into()],
            }],
        };
        Fixture {
            directory,
            store,
            spec,
        }
    }

    fn run_count(fixture: &Fixture) -> i64 {
        fixture
            .store
            .conn
            .query_row(
                "SELECT count(*) FROM export_runs WHERE action = ?1",
                [ACTION],
                |row| row.get(0),
            )
            .unwrap()
    }

    fn state(fixture: &Fixture, id: &str) -> Value {
        dossier_state(&fixture.store.conn, id).unwrap().summary
    }

    #[test]
    fn retirement_empties_bodies_and_replays_exactly() {
        let mut fixture = fixture();
        let untouched = state(&fixture, "XS-C");
        let report = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        for id in ["XS-A", "XS-B"] {
            let after = state(&fixture, id);
            assert_eq!(after["source_markdown"], "");
            assert_eq!(after["body"]["bytes"], 0);
            assert_eq!(after["has_full_transcript"], 0);
            assert_eq!(after["line_count"], 0);
            assert_eq!(after["content_kind"], RETIRED_DOSSIER_CONTENT_KIND);
            assert_eq!(after["authority_level"], RETIRED_DOSSIER_AUTHORITY_LEVEL);
            assert_eq!(after["title"], "Title");
            assert_eq!(after["slug"], id);
            assert_eq!(after["values"][0][2], "https://example.org/paper");
            assert_eq!(
                after["notes"],
                "Cached transcript. The transcription is held in the documents repositories."
            );
        }
        assert_eq!(state(&fixture, "XS-C"), untouched);
        let index = fixture
            .store
            .conn
            .query_row(
                "SELECT body_markdown, line_count FROM external_source_dossiers WHERE id = 'XS-I'",
                [],
                |row| Ok((row.get::<_, String>(0)?, row.get::<_, i64>(1)?)),
            )
            .unwrap();
        assert_eq!(index.0, "# Index\n\n- `XS-C`: `docs/c.md`\n");
        assert_eq!(index.1, index_body().lines().count() as i64 - 2);
        let edited = fixture
            .store
            .conn
            .query_row(
                "SELECT body_markdown, line_count FROM external_source_dossiers WHERE id = 'XS-E'",
                [],
                |row| Ok((row.get::<_, String>(0)?, row.get::<_, i64>(1)?)),
            )
            .unwrap();
        assert_eq!(
            edited.0,
            "# XS-E\n\n- Local PDF: held in the documents repositories.\n- Kept line.\n"
        );
        assert_eq!(edited.1, edited_body().lines().count() as i64 - 1);
        assert_eq!(
            state(&fixture, "XS-E")["values"],
            serde_json::json!([
                ["path_ref", 0, "data/y.pdf"],
                ["url_ref", 0, "https://example.org/paper"]
            ])
        );
        let refs = fixture
            .store
            .conn
            .query_row(
                "SELECT group_concat(ord || value, ',') FROM external_source_dossier_values \
                 WHERE dossier_id = 'XS-I' AND relation = 'path_ref'",
                [],
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(refs, "0docs/c.md");
        assert!(report["delta"].as_array().unwrap().len() >= 12);
        assert_eq!(
            fixture
                .store
                .retire_external_source_dossier_bodies(&fixture.spec, false)
                .unwrap(),
            report
        );
        assert_eq!(run_count(&fixture), 1);
        fixture.spec.reason.push_str(" changed");
        assert!(
            fixture
                .store
                .retire_external_source_dossier_bodies(&fixture.spec, false)
                .is_err()
        );
        fixture.spec.reason = "bytes are held in the documents repositories".into();
        fixture
            .store
            .conn
            .execute(
                "UPDATE external_source_dossiers SET title = 'drift' WHERE id = 'XS-A'",
                [],
            )
            .unwrap();
        assert!(
            fixture
                .store
                .retire_external_source_dossier_bodies(&fixture.spec, false)
                .is_err()
        );
    }

    #[test]
    fn evidence_and_database_file_hold_no_body_text() {
        let mut fixture = fixture();
        let report = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        assert!(!report.to_string().contains(MARKER));
        let details: String = fixture
            .store
            .conn
            .query_row(
                "SELECT details_json FROM export_runs WHERE action = ?1",
                [ACTION],
                |row| row.get(0),
            )
            .unwrap();
        assert!(!details.contains(MARKER));
        let bytes = fs::read(fixture.directory.join("test.sqlite3")).unwrap();
        assert!(
            !bytes
                .windows(MARKER.len())
                .any(|window| window == MARKER.as_bytes()),
            "free pages still hold a removed body"
        );
    }

    #[test]
    fn an_edit_only_specification_applies_without_a_retire_set() {
        let mut fixture = fixture();
        fixture.spec.retire.clear();
        fixture.spec.index = None;
        fixture.spec.custody_note.clear();
        let report = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        assert_eq!(report["dossiers"].as_array().unwrap().len(), 1);
        assert_eq!(state(&fixture, "XS-A")["body"]["bytes"], body("XS-A").len());
        fixture.spec.edit.clear();
        assert!(
            fixture
                .store
                .retire_external_source_dossier_bodies(&fixture.spec, false)
                .is_err()
        );
    }

    #[test]
    fn dry_run_reports_the_delta_and_leaves_the_store_unchanged() {
        let mut fixture = fixture();
        let before: Vec<Value> = ["XS-A", "XS-B", "XS-C", "XS-I"]
            .iter()
            .map(|id| state(&fixture, id))
            .collect();
        let report = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, true)
            .unwrap();
        assert_eq!(report["dry_run"], true);
        assert!(!report["delta"].as_array().unwrap().is_empty());
        let after: Vec<Value> = ["XS-A", "XS-B", "XS-C", "XS-I"]
            .iter()
            .map(|id| state(&fixture, id))
            .collect();
        assert_eq!(before, after);
        assert_eq!(run_count(&fixture), 0);
        let applied = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        assert_eq!(applied["delta"], report["delta"]);
    }

    #[test]
    fn retirement_rejects_invalid_admission_atomically() {
        for case in 0..13 {
            let mut fixture = fixture();
            let before: Vec<Value> = ["XS-A", "XS-B", "XS-I", "XS-E"]
                .iter()
                .map(|id| state(&fixture, id))
                .collect();
            match case {
                0 => fixture.spec.retire[0].expected_body_sha256 = sha256(b"other"),
                1 => fixture.spec.retire[0].expected_source_markdown = "docs/other.md".into(),
                2 => fixture.spec.retire[0].expected_line_count += 1,
                3 => fixture.spec.retire.push(fixture.spec.retire[0].clone()),
                4 => fixture.spec.retire[1].id = "XS-missing".into(),
                5 => fixture.spec.actor = " ".into(),
                6 => fixture.spec.custody_note.clear(),
                7 => fixture.spec.index.as_mut().unwrap().remove_body_lines[0] = "absent".into(),
                8 => fixture.spec.index.as_mut().unwrap().remove_path_refs[0] = "docs/z.md".into(),
                9 => {
                    fixture.spec.retire[0].expected_body_sha256 = "short".into();
                }
                10 => fixture.spec.edit[0].replace_body_lines[0].from = "absent".into(),
                11 => fixture.spec.edit[0].remove_path_refs = vec!["data/z.pdf".into()],
                12 => fixture.spec.edit[0].id = "XS-A".into(),
                _ => unreachable!(),
            }
            assert!(
                fixture
                    .store
                    .retire_external_source_dossier_bodies(&fixture.spec, false)
                    .is_err(),
                "case {case}"
            );
            let after: Vec<Value> = ["XS-A", "XS-B", "XS-I", "XS-E"]
                .iter()
                .map(|id| state(&fixture, id))
                .collect();
            assert_eq!(before, after, "case {case}");
            assert_eq!(run_count(&fixture), 0, "case {case}");
        }
    }

    #[test]
    fn retirement_rolls_back_late_trigger_failure() {
        let mut fixture = fixture();
        let before = state(&fixture, "XS-A");
        fixture
            .store
            .conn
            .execute_batch(
                "CREATE TRIGGER reject_second BEFORE UPDATE ON external_source_dossiers \
                 WHEN OLD.id = 'XS-B' BEGIN SELECT RAISE(ABORT, 'injected late failure'); END;",
            )
            .unwrap();
        assert!(
            fixture
                .store
                .retire_external_source_dossier_bodies(&fixture.spec, false)
                .is_err()
        );
        assert_eq!(state(&fixture, "XS-A"), before);
        assert_eq!(run_count(&fixture), 0);
    }

    #[test]
    fn ambiguous_index_line_is_rejected() {
        let mut fixture = fixture();
        let duplicated = format!("{}- `XS-A`: `docs/a.md`\n", index_body());
        fixture
            .store
            .conn
            .execute(
                "UPDATE external_source_dossiers SET body_markdown = ?1 WHERE id = 'XS-I'",
                [&duplicated],
            )
            .unwrap();
        fixture.spec.index.as_mut().unwrap().expected_body_sha256 = sha256(duplicated.as_bytes());
        let error = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap_err();
        assert!(error.to_string().contains("exactly once"), "{error:#}");
    }

    #[test]
    fn retired_dossier_emits_no_file_and_passes_invariants() {
        let mut fixture = fixture();
        fixture
            .store
            .conn
            .execute_batch(
                "INSERT INTO external_source_contracts VALUES ('SRC-T', 'data/t/*', 'https://example.org', \
                 'open', 'active', 'manual', '2026-01-01', '2026-01-02', ''); \
                 INSERT INTO external_source_dossiers_meta VALUES ('source_dossiers', '2026-11-01', 1, 'docs/*.md', 5);",
            )
            .unwrap();
        fs::create_dir(fixture.directory.join("docs")).unwrap();
        fixture
            .store
            .verify_external_source_invariants(&fixture.directory)
            .unwrap();
        let paths = |fixture: &Fixture| -> Vec<String> {
            fixture
                .store
                .render_external_sources_compat_outputs()
                .unwrap()
                .docs
                .iter()
                .map(|(path, _)| path.to_string())
                .collect()
        };
        assert_eq!(paths(&fixture).len(), 5);
        fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        assert_eq!(
            paths(&fixture),
            vec!["docs/c.md", "docs/e.md", "docs/index.md"]
        );
        fixture
            .store
            .verify_external_source_invariants(&fixture.directory)
            .unwrap();
    }

    #[test]
    fn empty_source_markdown_with_a_body_fails_the_invariant() {
        let fixture = fixture();
        fixture
            .store
            .conn
            .execute_batch(
                "INSERT INTO external_source_contracts VALUES ('SRC-T', 'data/t/*', 'https://example.org', \
                 'open', 'active', 'manual', '2026-01-01', '2026-01-02', ''); \
                 INSERT INTO external_source_dossiers_meta VALUES ('source_dossiers', '2026-11-01', 1, 'docs/*.md', 5); \
                 UPDATE external_source_dossiers SET source_markdown = '' WHERE id = 'XS-C';",
            )
            .unwrap();
        let error = fixture
            .store
            .verify_external_source_invariants(&fixture.directory)
            .unwrap_err();
        assert!(
            error.to_string().contains("XS-C has empty source_markdown"),
            "{error:#}"
        );
    }

    /// Inserts `survivor` and `removed` rows into a rowid table with an external-content full-text
    /// index, deletes `removed`, and leaves the index empty so only a rebuild can repopulate it.
    fn seed_desynchronized_index(fixture: &Fixture) {
        fixture
            .store
            .conn
            .execute_batch(
                "INSERT INTO claims (id, statement, status, where_stated, last_verified) VALUES \
                     ('C-1', 'alphaterm claim', 'open', '', ''), \
                     ('C-2', 'betaterm claim', 'open', '', ''); \
                 INSERT INTO insights (id, title, status, claim_refs_json) VALUES \
                     ('I-1', 'alphaterm insight', 'open', '[]'), \
                     ('I-2', 'betaterm insight', 'open', '[]'); \
                 INSERT INTO bibliography (id, title, authors) VALUES \
                     ('B-1', 'alphaterm paper', 'A'), ('B-2', 'betaterm paper', 'B'); \
                 INSERT INTO research_narratives (id, title, body_markdown) VALUES \
                     ('N-1', 'alphaterm note', 'text'), ('N-2', 'betaterm note', 'text'); \
                 DELETE FROM claims WHERE id = 'C-1'; \
                 DELETE FROM insights WHERE id = 'I-1'; \
                 DELETE FROM bibliography WHERE id = 'B-1'; \
                 DELETE FROM research_narratives WHERE id = 'N-1'; \
                 INSERT INTO claims_fts(claims_fts) VALUES('delete-all'); \
                 INSERT INTO insights_fts(insights_fts) VALUES('delete-all'); \
                 INSERT INTO bibliography_fts(bibliography_fts) VALUES('delete-all'); \
                 INSERT INTO research_narrative_search(research_narrative_search) VALUES('delete-all');",
            )
            .unwrap();
    }

    fn fts_hits(fixture: &Fixture, fts: &str, table: &str, term: &str) -> Vec<String> {
        let mut statement = fixture
            .store
            .conn
            .prepare(&format!(
                "SELECT t.id FROM {fts} f JOIN {table} t ON f.rowid = t.rowid \
                 WHERE {fts} MATCH ?1 ORDER BY t.id"
            ))
            .unwrap();
        statement
            .query_map([term], |row| row.get::<_, String>(0))
            .unwrap()
            .collect::<std::result::Result<_, _>>()
            .unwrap()
    }

    #[test]
    fn retirement_rebuilds_the_rowid_keyed_full_text_indexes() {
        let mut fixture = fixture();
        seed_desynchronized_index(&fixture);
        for (fts, table) in [
            ("claims_fts", "claims"),
            ("insights_fts", "insights"),
            ("bibliography_fts", "bibliography"),
            ("research_narrative_search", "research_narratives"),
        ] {
            assert!(fts_hits(&fixture, fts, table, "betaterm").is_empty());
        }
        fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        for (fts, table, survivor) in [
            ("claims_fts", "claims", "C-2"),
            ("insights_fts", "insights", "I-2"),
            ("bibliography_fts", "bibliography", "B-2"),
            ("research_narrative_search", "research_narratives", "N-2"),
        ] {
            assert_eq!(fts_hits(&fixture, fts, table, "betaterm"), [survivor]);
            assert!(
                fts_hits(&fixture, fts, table, "alphaterm").is_empty(),
                "{fts} still matches the deleted row"
            );
        }
    }

    #[test]
    fn a_failed_compaction_reports_the_committed_mutation() {
        let mut fixture = fixture();
        fixture.store.conn.execute_batch("BEGIN").unwrap();
        let error = compact_store(&mut fixture.store.conn).unwrap_err();
        fixture.store.conn.execute_batch("ROLLBACK").unwrap();
        let message = format!("{error:#}");
        assert!(
            message.contains("the retirement is committed, but VACUUM did not run"),
            "{message}"
        );
        assert!(!message.contains("not rebuilt"), "{message}");
        compact_store(&mut fixture.store.conn).unwrap();
    }

    #[test]
    fn replaying_an_applied_specification_retries_the_compaction() {
        let mut fixture = fixture();
        seed_desynchronized_index(&fixture);
        fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        fixture
            .store
            .conn
            .execute_batch("INSERT INTO claims_fts(claims_fts) VALUES('delete-all')")
            .unwrap();
        assert!(fts_hits(&fixture, "claims_fts", "claims", "betaterm").is_empty());
        fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        assert_eq!(
            fts_hits(&fixture, "claims_fts", "claims", "betaterm"),
            ["C-2"]
        );
        assert_eq!(run_count(&fixture), 1);
    }

    #[test]
    fn a_dossier_named_by_two_edits_or_an_edit_and_the_index_prune_is_rejected() {
        let mut fixture = fixture();
        let duplicate = fixture.spec.edit[0].clone();
        fixture.spec.edit.push(duplicate);
        let error = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("XS-E appears in more than one edit"),
            "{error:#}"
        );

        fixture.spec.edit.pop();
        fixture.spec.edit[0].id = "XS-I".into();
        let error = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("XS-I appears in more than one edit"),
            "{error:#}"
        );
        assert_eq!(run_count(&fixture), 0);
    }

    #[test]
    fn a_dry_run_against_an_applied_key_reports_the_replayed_content() {
        let mut fixture = fixture();
        let applied = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, false)
            .unwrap();
        let rehearsal = fixture
            .store
            .retire_external_source_dossier_bodies(&fixture.spec, true)
            .unwrap();
        assert_eq!(rehearsal["dry_run"], true);
        assert_eq!(rehearsal["already_applied"], true);
        assert_eq!(rehearsal["delta"], applied["delta"]);
        assert_eq!(rehearsal["dossiers"], applied["dossiers"]);
        assert_eq!(run_count(&fixture), 1);
    }
}
