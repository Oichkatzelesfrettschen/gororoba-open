//! Optimistic, atomic correction of theorem titles and formal claim relations.
//!
//! The immutable proof locator anchors each correction. The existing append-only
//! theorem identity event stream retains the specification and both states.

use anyhow::{Context, Result, bail};
use chrono::DateTime;
use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeSet, path::Path};

use crate::{ProvenanceStore, sha256_hex};

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoremLinkCorrectionSpec {
    pub correction_key: String,
    pub actor: String,
    pub reason: String,
    pub applied_at: String,
    #[serde(rename = "correction")]
    pub corrections: Vec<TheoremLinkCorrection>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoremLinkCorrection {
    pub stable_id: String,
    /// Exact existing locator; correction cannot change the proof path.
    pub proof_path: String,
    pub expected_title: String,
    pub expected_claim_ids: Vec<String>,
    pub title: String,
    pub claim_ids: Vec<String>,
    /// Both assumption fields must be supplied together or both omitted.
    pub expected_assumptions: Option<String>,
    pub assumptions: Option<String>,
}

/// Complete identity and theorem projection, with sorted formal claim links.
#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoremLinkState {
    pub stable_id: String,
    pub legacy_name: String,
    pub proof_path: String,
    pub identity_kind: String,
    pub assumptions: String,
    pub kernel_result: String,
    pub replay_command: String,
    pub falsifier: String,
    pub identity_source: String,
    pub title: String,
    pub theorem_status: String,
    pub theorem_source: String,
    pub claim_ids: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoremLinkCorrectionChange {
    pub before: TheoremLinkState,
    pub after: TheoremLinkState,
}

#[derive(Clone, Debug, Serialize)]
pub struct TheoremLinkCorrectionResult {
    pub correction_key: String,
    pub event_key: String,
    pub spec_sha256: String,
    pub changes: Vec<TheoremLinkCorrectionChange>,
    pub exact_replay: bool,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct CorrectionEnvelope {
    schema_version: u32,
    operation: String,
    specification: TheoremLinkCorrectionSpec,
    raw_spec: String,
    changes: Vec<TheoremLinkCorrectionChange>,
}

pub fn parse_theorem_link_correction_spec(raw: &str) -> Result<TheoremLinkCorrectionSpec> {
    if raw.trim().is_empty() || !raw.is_ascii() {
        bail!("theorem link correction specification must be nonempty ASCII TOML");
    }
    let spec: TheoremLinkCorrectionSpec =
        toml::from_str(raw).context("parse theorem link correction TOML")?;
    for (field, value) in [
        ("correction_key", spec.correction_key.as_str()),
        ("actor", spec.actor.as_str()),
        ("reason", spec.reason.as_str()),
        ("applied_at", spec.applied_at.as_str()),
    ] {
        nonempty_ascii(field, value)?;
    }
    DateTime::parse_from_rfc3339(&spec.applied_at).context("applied_at must be RFC3339")?;
    if spec.corrections.is_empty() {
        bail!("theorem link correction requires at least one correction");
    }
    let mut identities = BTreeSet::new();
    for correction in &spec.corrections {
        for (field, value) in [
            ("stable_id", correction.stable_id.as_str()),
            ("proof_path", correction.proof_path.as_str()),
            ("expected_title", correction.expected_title.as_str()),
            ("title", correction.title.as_str()),
        ] {
            nonempty_ascii(field, value)?;
        }
        if !correction.stable_id.starts_with("THM-") {
            bail!("stable_id must start with THM-: {}", correction.stable_id);
        }
        if !identities.insert(&correction.stable_id) {
            bail!("duplicate theorem correction {}", correction.stable_id);
        }
        if Path::new(&correction.proof_path)
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
        {
            bail!("proof_path must be a repository-relative normal path");
        }
        for (field, values) in [
            ("expected_claim_ids", &correction.expected_claim_ids),
            ("claim_ids", &correction.claim_ids),
        ] {
            let mut distinct = BTreeSet::new();
            for value in values {
                nonempty_ascii(field, value)?;
                if !distinct.insert(value) {
                    bail!("{field} contains duplicate claim {value}");
                }
            }
        }
        match (&correction.expected_assumptions, &correction.assumptions) {
            (None, None) => {}
            (Some(expected), Some(assumptions)) => {
                if !expected.is_ascii() {
                    bail!("expected_assumptions must be ASCII");
                }
                nonempty_ascii("assumptions", assumptions)?;
            }
            _ => bail!("expected_assumptions and assumptions must be supplied together"),
        }
    }
    Ok(spec)
}

fn nonempty_ascii(field: &str, value: &str) -> Result<()> {
    if value.trim().is_empty() || !value.is_ascii() {
        bail!("{field} must be nonempty ASCII");
    }
    Ok(())
}

impl ProvenanceStore {
    pub fn correct_theorem_links(
        &mut self,
        repo_root: &Path,
        spec: &TheoremLinkCorrectionSpec,
        raw_spec: &str,
    ) -> Result<TheoremLinkCorrectionResult> {
        // Bind the audited bytes to the typed input even for non-CLI callers.
        if parse_theorem_link_correction_spec(raw_spec)? != *spec {
            bail!("typed theorem correction disagrees with raw specification");
        }
        let spec_sha256 = sha256_hex(raw_spec);
        let event_key = format!("correct-links:{}", spec.correction_key);
        let transaction = self
            .conn
            .transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
        let retained: Option<(String, String)> = transaction
            .query_row(
                "SELECT spec_sha256, reason FROM theorem_identity_events WHERE binding_key = ?1",
                params![event_key],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()?;
        if let Some((retained_hash, retained_reason)) = retained {
            if retained_hash != spec_sha256 {
                bail!("theorem correction key already exists with a different content hash");
            }
            let envelope: CorrectionEnvelope = serde_json::from_str(&retained_reason)
                .context("parse retained theorem correction envelope")?;
            if envelope.schema_version != 1
                || envelope.operation != "correct_theorem_links"
                || envelope.specification != *spec
                || envelope.raw_spec != raw_spec
                || envelope.changes.len() != spec.corrections.len()
            {
                bail!("retained theorem correction envelope disagrees with specification");
            }
            for correction in &spec.corrections {
                let retained_change = envelope
                    .changes
                    .iter()
                    .find(|change| change.after.stable_id == correction.stable_id)
                    .context("retained theorem correction is missing an identity")?;
                let current = read_state(&transaction, &correction.stable_id)?;
                if current != retained_change.after {
                    bail!(
                        "theorem correction replay poststate has changed: {}",
                        current.stable_id
                    );
                }
                validate_result(&transaction, repo_root, &current)?;
            }
            transaction.commit()?;
            return Ok(TheoremLinkCorrectionResult {
                correction_key: spec.correction_key.clone(),
                event_key,
                spec_sha256,
                changes: envelope.changes,
                exact_replay: true,
            });
        }

        let mut ordered = spec.corrections.iter().collect::<Vec<_>>();
        ordered.sort_by(|left, right| left.stable_id.cmp(&right.stable_id));
        let mut changes = Vec::with_capacity(ordered.len());
        for correction in ordered {
            let before = read_state(&transaction, &correction.stable_id)?;
            let mut expected_claim_ids = correction.expected_claim_ids.clone();
            expected_claim_ids.sort();
            if before.proof_path != correction.proof_path
                || before.title != correction.expected_title
                || before.claim_ids != expected_claim_ids
                || correction
                    .expected_assumptions
                    .as_ref()
                    .is_some_and(|expected| expected != &before.assumptions)
            {
                bail!(
                    "stale theorem correction prestate: {}",
                    correction.stable_id
                );
            }
            let mut after = before.clone();
            after.title.clone_from(&correction.title);
            after.claim_ids.clone_from(&correction.claim_ids);
            after.claim_ids.sort();
            if let Some(assumptions) = &correction.assumptions {
                after.assumptions.clone_from(assumptions);
            }
            validate_result(&transaction, repo_root, &after)?;
            changes.push(TheoremLinkCorrectionChange { before, after });
        }

        for change in &changes {
            let after = &change.after;
            transaction.execute(
                "DELETE FROM theorem_claim_links WHERE theorem_stable_id = ?1",
                params![after.stable_id],
            )?;
            for claim_id in &after.claim_ids {
                transaction.execute(
                    "INSERT INTO theorem_claim_links (theorem_stable_id, claim_id, relation_kind)
                     VALUES (?1, ?2, 'formal_proposition')",
                    params![after.stable_id, claim_id],
                )?;
            }
            let identity_count = transaction.execute(
                "UPDATE theorem_identities SET assumptions = ?2 WHERE stable_id = ?1",
                params![after.stable_id, after.assumptions],
            )?;
            let projection_count = transaction.execute(
                "UPDATE theorems SET title = ?2, linked_claim_ids_json = ?3 WHERE id = ?1",
                params![
                    after.legacy_name,
                    after.title,
                    serde_json::to_string(&after.claim_ids)?
                ],
            )?;
            if identity_count != 1 || projection_count != 1 {
                bail!("theorem correction requires one identity and one projection");
            }
            if read_state(&transaction, &after.stable_id)? != *after {
                bail!("theorem correction poststate disagrees with requested result");
            }
        }

        let theorem_ids: Vec<_> = changes
            .iter()
            .map(|change| &change.after.stable_id)
            .collect();
        let claim_ids: BTreeSet<_> = changes
            .iter()
            .flat_map(|change| &change.after.claim_ids)
            .collect();
        let envelope = CorrectionEnvelope {
            schema_version: 1,
            operation: "correct_theorem_links".to_owned(),
            specification: spec.clone(),
            raw_spec: raw_spec.to_owned(),
            changes: changes.clone(),
        };
        transaction.execute(
            "INSERT INTO theorem_identity_events (
                 binding_key, spec_sha256, actor, reason, applied_at,
                 theorem_ids_json, claim_ids_json
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
            params![
                event_key,
                spec_sha256,
                spec.actor,
                serde_json::to_string(&envelope)?,
                spec.applied_at,
                serde_json::to_string(&theorem_ids)?,
                serde_json::to_string(&claim_ids)?,
            ],
        )?;
        transaction.commit()?;
        Ok(TheoremLinkCorrectionResult {
            correction_key: spec.correction_key.clone(),
            event_key,
            spec_sha256,
            changes,
            exact_replay: false,
        })
    }
}

fn read_state(connection: &Connection, stable_id: &str) -> Result<TheoremLinkState> {
    let (mut state, projected_path, projected_links): (TheoremLinkState, String, String) =
        connection
            .query_row(
                "SELECT identity.stable_id, identity.legacy_name, identity.proof_path,
                    identity.identity_kind, identity.assumptions, identity.kernel_result,
                    identity.replay_command, identity.falsifier, identity.source,
                    theorem.title, theorem.status, theorem.source,
                    theorem.proof_path, theorem.linked_claim_ids_json
             FROM theorem_identities AS identity
             JOIN theorems AS theorem ON theorem.id = identity.legacy_name
             WHERE identity.stable_id = ?1",
                params![stable_id],
                |row| {
                    Ok((
                        TheoremLinkState {
                            stable_id: row.get(0)?,
                            legacy_name: row.get(1)?,
                            proof_path: row.get(2)?,
                            identity_kind: row.get(3)?,
                            assumptions: row.get(4)?,
                            kernel_result: row.get(5)?,
                            replay_command: row.get(6)?,
                            falsifier: row.get(7)?,
                            identity_source: row.get(8)?,
                            title: row.get(9)?,
                            theorem_status: row.get(10)?,
                            theorem_source: row.get(11)?,
                            claim_ids: Vec::new(),
                        },
                        row.get(12)?,
                        row.get(13)?,
                    ))
                },
            )
            .with_context(|| format!("read theorem identity and projection {stable_id}"))?;
    let mut statement = connection.prepare(
        "SELECT claim_id, relation_kind FROM theorem_claim_links
         WHERE theorem_stable_id = ?1 ORDER BY claim_id",
    )?;
    let links = statement.query_map(params![stable_id], |row| {
        Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?))
    })?;
    for link in links {
        let (claim_id, relation_kind) = link?;
        if relation_kind != "formal_proposition" {
            bail!("unsupported theorem relation kind {relation_kind}");
        }
        state.claim_ids.push(claim_id);
    }
    let mut projected: Vec<String> = serde_json::from_str(&projected_links)?;
    projected.sort();
    if projected_path != state.proof_path || projected != state.claim_ids {
        bail!("theorem projection disagrees with identity or claim relations: {stable_id}");
    }
    Ok(state)
}

fn validate_result(
    connection: &Connection,
    repo_root: &Path,
    state: &TheoremLinkState,
) -> Result<()> {
    if !repo_root.join(&state.proof_path).is_file() {
        bail!("theorem proof path is missing: {}", state.proof_path);
    }
    if state.identity_kind == "explicit_link" && state.claim_ids.is_empty() {
        bail!("explicit_link theorem requires at least one claim relation");
    }
    for claim_id in &state.claim_ids {
        let (formal_proof, where_stated, status_note): (Option<String>, String, Option<String>) =
            connection
                .query_row(
                    "SELECT formal_proof, where_stated, status_note FROM claims WHERE id = ?1",
                    params![claim_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                )
                .with_context(|| format!("theorem relation claim is missing: {claim_id}"))?;
        if formal_proof.as_deref() != Some(&state.proof_path)
            && !contains_proof_locator(&where_stated, &state.proof_path)
            && !status_note
                .as_deref()
                .is_some_and(|note| contains_proof_locator(note, &state.proof_path))
        {
            bail!(
                "claim {claim_id} has no matching proof locator {}",
                state.proof_path
            );
        }
    }
    Ok(())
}

fn contains_proof_locator(text: &str, proof_path: &str) -> bool {
    let path_character = |character: char| {
        character.is_alphanumeric() || matches!(character, '/' | '\\' | '_' | '-' | '.')
    };
    text.match_indices(proof_path).any(|(start, _)| {
        let end = start + proof_path.len();
        !text[..start]
            .chars()
            .next_back()
            .is_some_and(path_character)
            && !text[end..].chars().next().is_some_and(path_character)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::PathBuf,
        time::{SystemTime, UNIX_EPOCH},
    };

    struct Fixture {
        store: ProvenanceStore,
        root: PathBuf,
    }

    impl Fixture {
        fn new() -> Result<Self> {
            let mut connection = Connection::open_in_memory()?;
            connection.pragma_update(None, "foreign_keys", "ON")?;
            crate::migrations::migrations().to_latest(&mut connection)?;
            for (claim_id, proof) in [
                ("C-1", "proof.v"),
                ("C-2", "unrelated.v"),
                ("C-3", "proof.v"),
                ("C-4", "proof.v.bak"),
            ] {
                connection.execute(
                    "INSERT INTO claims (
                        id, statement, status, where_stated, last_verified,
                        formal_proof, status_note, compat_toml_text
                     ) VALUES (?1, 'formal proposition', 'Verified', ?2,
                               '2026-10-11', ?2, NULL, '')",
                    params![claim_id, proof],
                )?;
            }
            connection.execute_batch(
                "INSERT INTO theorems (id, title, proof_path, status, linked_claim_ids_json, source)
                 VALUES ('Legacy', 'Overbroad title', 'proof.v', 'verified',
                         '[\"C-1\",\"C-2\"]', 'test projection');
                 INSERT INTO theorem_identities (
                     stable_id, legacy_name, proof_path, identity_kind, assumptions,
                     kernel_result, replay_command, falsifier, source
                 ) VALUES ('THM-TEST', 'Legacy', 'proof.v', 'explicit_link', 'Axiom A',
                           'Qed', 'rocq compile proof.v', 'kernel rejection', 'test identity');
                 INSERT INTO theorem_claim_links (theorem_stable_id, claim_id, relation_kind)
                 VALUES ('THM-TEST', 'C-1', 'formal_proposition'),
                        ('THM-TEST', 'C-2', 'formal_proposition');",
            )?;
            let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
            let root = std::env::temp_dir().join(format!(
                "gororoba-theorem-link-correction-{}-{nonce}",
                std::process::id()
            ));
            fs::create_dir(&root)?;
            fs::write(
                root.join("proof.v"),
                "Theorem fixture : True. Proof. exact I. Qed.\n",
            )?;
            Ok(Self {
                store: ProvenanceStore { conn: connection },
                root,
            })
        }

        fn state(&self) -> Result<TheoremLinkState> {
            read_state(&self.store.conn, "THM-TEST")
        }

        fn event_count(&self) -> Result<i64> {
            Ok(self.store.conn.query_row(
                "SELECT COUNT(*) FROM theorem_identity_events",
                [],
                |row| row.get(0),
            )?)
        }

        fn apply(
            &mut self,
            spec: &TheoremLinkCorrectionSpec,
        ) -> Result<TheoremLinkCorrectionResult> {
            let raw = toml::to_string(spec)?;
            self.store.correct_theorem_links(&self.root, spec, &raw)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_file(self.root.join("proof.v"));
            let _ = fs::remove_dir(&self.root);
        }
    }

    fn correction_spec() -> TheoremLinkCorrectionSpec {
        TheoremLinkCorrectionSpec {
            correction_key: "formal-proposition-correction".to_owned(),
            actor: "test-actor".to_owned(),
            reason: "Remove a mismatched interpretation and record kernel assumptions".to_owned(),
            applied_at: "2026-10-11T00:00:00Z".to_owned(),
            corrections: vec![TheoremLinkCorrection {
                stable_id: "THM-TEST".to_owned(),
                proof_path: "proof.v".to_owned(),
                expected_title: "Overbroad title".to_owned(),
                expected_claim_ids: vec!["C-2".to_owned(), "C-1".to_owned()],
                title: "Bounded formal proposition".to_owned(),
                claim_ids: vec!["C-3".to_owned(), "C-1".to_owned()],
                expected_assumptions: Some("Axiom A".to_owned()),
                assumptions: Some("Axiom A; Axiom B".to_owned()),
            }],
        }
    }

    #[test]
    fn theorem_link_correction_retains_both_states_and_exact_replay() -> Result<()> {
        let mut fixture = Fixture::new()?;
        let before = fixture.state()?;
        let spec = correction_spec();
        let result = fixture.apply(&spec)?;
        assert!(!result.exact_replay);
        assert_eq!(result.changes[0].before, before);
        let after = fixture.state()?;
        assert_eq!(result.changes[0].after, after);
        assert_eq!(after.claim_ids, ["C-1", "C-3"]);
        assert_eq!(after.assumptions, "Axiom A; Axiom B");
        assert_eq!(after.title, "Bounded formal proposition");
        assert_eq!(after.proof_path, before.proof_path);
        let retained: String = fixture.store.conn.query_row(
            "SELECT reason FROM theorem_identity_events WHERE binding_key = ?1",
            params![result.event_key],
            |row| row.get(0),
        )?;
        let envelope: CorrectionEnvelope = serde_json::from_str(&retained)?;
        assert_eq!(envelope.specification, spec);
        assert_eq!(envelope.raw_spec, toml::to_string(&spec)?);
        assert_eq!(envelope.changes, result.changes);
        assert_eq!(fixture.event_count()?, 1);

        let replay = fixture.apply(&spec)?;
        assert!(replay.exact_replay);
        assert_eq!(replay.changes, result.changes);
        assert_eq!(fixture.state()?, after);
        assert_eq!(fixture.event_count()?, 1);
        assert!(
            fixture
                .store
                .conn
                .execute(
                    "UPDATE theorem_identity_events SET reason = 'overwrite'",
                    []
                )
                .is_err()
        );
        assert!(
            fixture
                .store
                .conn
                .execute("DELETE FROM theorem_identity_events", [])
                .is_err()
        );
        Ok(())
    }

    #[test]
    fn theorem_link_correction_rejects_stale_and_invalid_inputs_atomically() -> Result<()> {
        for invalid_case in 0..9 {
            let mut fixture = Fixture::new()?;
            let before = fixture.state()?;
            let mut spec = correction_spec();
            let correction = &mut spec.corrections[0];
            match invalid_case {
                0 => correction.expected_title = "stale title".to_owned(),
                1 => correction.expected_claim_ids = vec!["C-1".to_owned()],
                2 => correction.proof_path = "other.v".to_owned(),
                3 => correction.expected_assumptions = Some("stale assumptions".to_owned()),
                4 => correction.claim_ids = vec!["C-missing".to_owned()],
                5 => correction.claim_ids = vec!["C-2".to_owned()],
                6 => correction.claim_ids = vec!["C-4".to_owned()],
                7 => correction.claim_ids.clear(),
                8 => fs::remove_file(fixture.root.join("proof.v"))?,
                _ => unreachable!(),
            }
            assert!(fixture.apply(&spec).is_err(), "invalid case {invalid_case}");
            assert_eq!(fixture.state()?, before);
            assert_eq!(fixture.event_count()?, 0);
        }
        Ok(())
    }

    #[test]
    fn theorem_link_correction_batch_and_history_failure_roll_back() -> Result<()> {
        let mut fixture = Fixture::new()?;
        let before = fixture.state()?;
        let mut spec = correction_spec();
        let mut missing = spec.corrections[0].clone();
        missing.stable_id = "THM-MISSING".to_owned();
        spec.corrections.push(missing);
        assert!(fixture.apply(&spec).is_err());
        assert_eq!(fixture.state()?, before);
        assert_eq!(fixture.event_count()?, 0);

        fixture.store.conn.execute_batch(
            "CREATE TRIGGER fail_correction_history
             BEFORE INSERT ON theorem_identity_events
             BEGIN SELECT RAISE(ABORT, 'history write unavailable'); END;",
        )?;
        let failure = fixture
            .apply(&correction_spec())
            .expect_err("history must be retained");
        assert!(failure.to_string().contains("history write unavailable"));
        assert_eq!(fixture.state()?, before);
        assert_eq!(fixture.event_count()?, 0);
        Ok(())
    }

    #[test]
    fn theorem_link_correction_replay_rejects_changed_bytes_and_poststate() -> Result<()> {
        let mut fixture = Fixture::new()?;
        let spec = correction_spec();
        fixture.apply(&spec)?;
        let after = fixture.state()?;
        let raw = format!("{}\n", toml::to_string(&spec)?);
        assert!(
            fixture
                .store
                .correct_theorem_links(&fixture.root, &spec, &raw)
                .is_err()
        );
        let mut altered = spec.clone();
        altered.reason = "different justification".to_owned();
        assert!(fixture.apply(&altered).is_err());
        assert_eq!(fixture.state()?, after);
        fixture.store.conn.execute(
            "UPDATE theorem_identities SET assumptions = 'changed after correction'
             WHERE stable_id = 'THM-TEST'",
            [],
        )?;
        let changed = fixture.state()?;
        assert!(fixture.apply(&spec).is_err());
        assert_eq!(fixture.state()?, changed);
        assert_eq!(fixture.event_count()?, 1);
        Ok(())
    }

    #[test]
    fn theorem_link_correction_assumptions_are_optional_and_raw_input_is_bound() -> Result<()> {
        let mut fixture = Fixture::new()?;
        let before = fixture.state()?;
        let mut spec = correction_spec();
        let raw = toml::to_string(&spec)?;
        spec.reason = "an altered typed input".to_owned();
        assert!(
            fixture
                .store
                .correct_theorem_links(&fixture.root, &spec, &raw)
                .is_err()
        );
        assert_eq!(fixture.state()?, before);
        assert_eq!(fixture.event_count()?, 0);

        spec.corrections[0].expected_assumptions = None;
        spec.corrections[0].assumptions = None;
        fixture.apply(&spec)?;
        assert_eq!(fixture.state()?.assumptions, before.assumptions);
        Ok(())
    }

    #[test]
    fn theorem_link_correction_accepts_explicit_prose_locators() -> Result<()> {
        let mut fixture = Fixture::new()?;
        fixture.store.conn.execute(
            "UPDATE claims SET formal_proof = NULL,
             where_stated = 'See `proof.v` for the formal proposition' WHERE id = 'C-1'",
            [],
        )?;
        fixture.store.conn.execute(
            "UPDATE claims SET formal_proof = NULL, where_stated = 'source document',
             status_note = 'Formal proof: proof.v; assumptions retained' WHERE id = 'C-3'",
            [],
        )?;
        fixture.apply(&correction_spec())?;
        assert_eq!(fixture.state()?.claim_ids, ["C-1", "C-3"]);
        Ok(())
    }

    #[test]
    fn theorem_link_correction_parser_requires_unambiguous_preconditions() -> Result<()> {
        for invalid_case in 0..5 {
            let mut spec = correction_spec();
            match invalid_case {
                0 => spec.corrections[0].expected_assumptions = None,
                1 => spec.corrections[0]
                    .expected_claim_ids
                    .push("C-1".to_owned()),
                2 => spec.corrections[0].claim_ids.push("C-1".to_owned()),
                3 => spec.corrections[0].proof_path = "../proof.v".to_owned(),
                4 => spec.corrections.push(spec.corrections[0].clone()),
                _ => unreachable!(),
            }
            assert!(parse_theorem_link_correction_spec(&toml::to_string(&spec)?).is_err());
        }
        let raw = toml::to_string(&correction_spec())?;
        assert!(parse_theorem_link_correction_spec(&format!("unknown_field = 1\n{raw}")).is_err());
        Ok(())
    }

    #[test]
    fn theorem_link_correction_locator_requires_complete_path() {
        assert!(contains_proof_locator(
            "See `proofs/equal_norm.v`",
            "proofs/equal_norm.v"
        ));
        assert!(contains_proof_locator(
            "proofs/equal_norm.v; theorem",
            "proofs/equal_norm.v"
        ));
        assert!(!contains_proof_locator(
            "proofs/equal_norm.v.bak",
            "proofs/equal_norm.v"
        ));
        assert!(!contains_proof_locator(
            "other/proofs/equal_norm.v",
            "proofs/equal_norm.v"
        ));
    }
}
