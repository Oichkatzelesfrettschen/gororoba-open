//! Source-bound kernel evidence and non-destructive proof inventory synchronization.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
};

use anyhow::{Context, Result, bail, ensure};
use chrono::DateTime;
use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{ProvenanceStore, TheoremLinkState, sha256_hex, theorem_link_correction::read_state};

pub const SOURCE_ONLY: &str = "source_only";
pub const KERNEL_CHECKED: &str = "kernel_checked";

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ProofFileDigest {
    pub path: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ProofDeclarationEvidence {
    pub name: String,
    pub statement: String,
    pub assumptions: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TheoremKernelWitness {
    pub schema_version: u32,
    pub stable_id: String,
    pub proof_path: String,
    pub project_sha256: String,
    pub sources: Vec<ProofFileDigest>,
    pub compile_log: ProofFileDigest,
    pub kernel_log: ProofFileDigest,
    pub assumption_log: ProofFileDigest,
    pub proof_object: ProofFileDigest,
    pub compile_command: String,
    pub kernel_command: String,
    pub toolchain: String,
    pub compile_exit_code: i32,
    pub kernel_exit_code: i32,
    pub warning_policy: String,
    pub declarations: Vec<ProofDeclarationEvidence>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoremKernelEvidenceSpec {
    pub evidence_key: String,
    pub actor: String,
    pub reason: String,
    pub applied_at: String,
    pub expected_kernel_result_sha256: String,
    pub expected_status: String,
    pub witness: TheoremKernelWitness,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoremInventorySyncSpec {
    pub sync_key: String,
    pub actor: String,
    pub reason: String,
    pub applied_at: String,
    pub project_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct TheoremEvidenceMutationResult {
    pub event_key: String,
    pub theorem_count: usize,
    pub source_only_count: usize,
    pub kernel_checked_count: usize,
    pub exact_replay: bool,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct KernelEvidenceEnvelope {
    schema_version: u32,
    specification: TheoremKernelEvidenceSpec,
    raw_spec: String,
    before: TheoremLinkState,
    after: TheoremLinkState,
}

fn text(value: &str, label: &str) -> Result<()> {
    ensure!(
        !value.trim().is_empty() && value.is_ascii(),
        "{label} must be nonempty ASCII"
    );
    Ok(())
}

fn digest(value: &str, label: &str) -> Result<()> {
    ensure!(
        value.len() == 64
            && value
                .bytes()
                .all(|character| character.is_ascii_digit() || (b'a'..=b'f').contains(&character)),
        "{label} must be a lowercase SHA-256 digest"
    );
    Ok(())
}

fn metadata(key: &str, actor: &str, reason: &str, applied_at: &str) -> Result<()> {
    for (value, label) in [(key, "event key"), (actor, "actor"), (reason, "reason")] {
        text(value, label)?;
    }
    DateTime::parse_from_rfc3339(applied_at).context("applied_at must be RFC3339")?;
    Ok(())
}

pub fn parse_theorem_kernel_evidence_spec(raw: &str) -> Result<TheoremKernelEvidenceSpec> {
    let specification: TheoremKernelEvidenceSpec =
        toml::from_str(raw).context("parse theorem kernel evidence specification")?;
    metadata(
        &specification.evidence_key,
        &specification.actor,
        &specification.reason,
        &specification.applied_at,
    )?;
    digest(
        &specification.expected_kernel_result_sha256,
        "expected kernel result",
    )?;
    ensure!(
        matches!(
            specification.expected_status.as_str(),
            SOURCE_ONLY | KERNEL_CHECKED
        ),
        "unsupported expected theorem status"
    );
    Ok(specification)
}

pub fn parse_theorem_inventory_sync_spec(raw: &str) -> Result<TheoremInventorySyncSpec> {
    let specification: TheoremInventorySyncSpec =
        toml::from_str(raw).context("parse theorem inventory synchronization specification")?;
    metadata(
        &specification.sync_key,
        &specification.actor,
        &specification.reason,
        &specification.applied_at,
    )?;
    digest(&specification.project_sha256, "proof project")?;
    Ok(specification)
}

pub(crate) fn file_sha256(path: &Path) -> Result<String> {
    let contents =
        fs::read(path).with_context(|| format!("read evidence input {}", path.display()))?;
    Ok(Sha256::digest(contents)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn local_file(root: &Path, relative: &str) -> Result<PathBuf> {
    text(relative, "evidence path")?;
    ensure!(
        Path::new(relative)
            .components()
            .all(|part| matches!(part, Component::Normal(_))),
        "evidence path must be repository-relative: {relative}"
    );
    let mut candidate = root.to_path_buf();
    for component in Path::new(relative).components() {
        candidate.push(component.as_os_str());
        ensure!(
            !fs::symlink_metadata(&candidate)?.file_type().is_symlink(),
            "evidence path contains a symbolic link: {relative}"
        );
    }
    ensure!(
        fs::symlink_metadata(&candidate)?.file_type().is_file(),
        "evidence input must be a regular file: {relative}"
    );
    let canonical = candidate.canonicalize()?;
    ensure!(
        canonical.starts_with(root.canonicalize()?),
        "evidence input escapes the repository: {relative}"
    );
    Ok(candidate)
}

fn verify_file(root: &Path, evidence: &ProofFileDigest) -> Result<PathBuf> {
    digest(&evidence.sha256, "evidence SHA-256")?;
    let path = local_file(root, &evidence.path)?;
    ensure!(
        file_sha256(&path)? == evidence.sha256,
        "evidence digest changed: {}",
        evidence.path
    );
    Ok(path)
}

fn source_commands(source: &str) -> Result<Vec<String>> {
    let characters = source.chars().collect::<Vec<_>>();
    let mut cursor = 0;
    let mut depth = 0;
    let mut quoted = false;
    let mut visible = String::new();
    let mut commands = Vec::new();
    while cursor < characters.len() {
        let character = characters[cursor];
        let next = characters.get(cursor + 1).copied();
        if !quoted && character == '(' && next == Some('*') {
            depth += 1;
            cursor += 2;
            continue;
        }
        if depth > 0 && character == '*' && next == Some(')') {
            depth -= 1;
            cursor += 2;
            visible.push(' ');
            continue;
        }
        if depth == 0 {
            if character == '"' {
                quoted = !quoted;
                visible.push(character);
            } else if !quoted
                && character == '.'
                && next.is_none_or(|next| next.is_whitespace() || next == '(')
            {
                if !visible.trim().is_empty() {
                    commands.push(visible.trim().to_owned());
                }
                visible.clear();
            } else {
                visible.push(character);
            }
        }
        cursor += 1;
    }
    ensure!(
        depth == 0 && !quoted,
        "proof source has an unterminated comment or string"
    );
    if !visible.trim().is_empty() {
        commands.push(visible.trim().to_owned());
    }
    Ok(commands)
}

fn validate_execution_commands(witness: &TheoremKernelWitness) -> Result<()> {
    let compiler = witness
        .compile_command
        .split_whitespace()
        .collect::<Vec<_>>();
    let checker = witness
        .kernel_command
        .split_whitespace()
        .collect::<Vec<_>>();
    let tool_name = |token: &str| {
        Path::new(token)
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or_default()
            .to_owned()
    };
    ensure!(
        compiler.iter().any(|token| tool_name(token) == "coqc")
            || compiler
                .windows(2)
                .any(|pair| tool_name(pair[0]) == "rocq" && pair[1] == "compile"),
        "compiler command must name rocq compile or coqc"
    );
    ensure!(
        checker
            .iter()
            .any(|token| matches!(tool_name(token).as_str(), "rocqchk" | "coqchk"))
            || checker
                .windows(2)
                .any(|pair| tool_name(pair[0]) == "rocq" && pair[1] == "check"),
        "kernel command must name rocq check, rocqchk, or coqchk"
    );
    ensure!(
        !compiler.iter().chain(&checker).any(|token| matches!(
            *token,
            "-vos" | "-vok" | "-vio" | "-quick" | "-admit" | "-norec"
        )),
        "kernel evidence rejects abbreviated compilation or admitted dependencies"
    );
    let source = witness
        .proof_path
        .strip_prefix("proofs/")
        .context("proof locator must start with proofs/")?;
    ensure!(
        compiler
            .iter()
            .any(|token| *token == source || *token == witness.proof_path),
        "compiler command must name the witnessed source"
    );
    let module = source
        .strip_suffix(".v")
        .context("proof locator must end with .v")?
        .split_once('/')
        .context("proof locator lacks source root")?;
    let namespace = if module.0 == "theories" {
        "OpenGororoba"
    } else {
        "OpenGororobaVerified"
    };
    let logical_module = format!("{namespace}.{}", module.1.replace('/', "."));
    ensure!(
        checker.contains(&logical_module.as_str()),
        "kernel command must name {logical_module}"
    );
    if let Some(policy) = match witness.warning_policy.as_str() {
        "fatal_all" => Some("+all"),
        "fatal_default" => Some("+default"),
        _ => None,
    } {
        ensure!(
            compiler.windows(2).any(|pair| pair == ["-w", policy])
                && compiler
                    .windows(2)
                    .filter(|pair| pair[0] == "-w")
                    .all(|pair| pair[1] == policy)
                && compiler.last() != Some(&"-w"),
            "compiler command disagrees with the fatal warning policy"
        );
    }
    Ok(())
}

fn validate_assumption_report(report: &str, assumptions: &[String]) -> Result<()> {
    let mut expected = BTreeSet::new();
    for assumption in assumptions {
        text(assumption, "declared assumption")?;
        ensure!(
            expected.insert(assumption.as_str()),
            "duplicate declared assumption: {assumption}"
        );
    }
    let mut observed = BTreeSet::new();
    let mut assumption_section = false;
    let mut closed = false;
    for original in report.lines() {
        let line = original
            .strip_prefix("Rocq < ")
            .or_else(|| original.strip_prefix("Coq < "))
            .unwrap_or(original);
        let trimmed = line.trim();
        if trimmed == "Axioms:" || trimmed == "Section Variables:" {
            ensure!(
                !closed,
                "assumption log combines a closed context with assumptions"
            );
            assumption_section = true;
        } else if trimmed == "Closed under the global context" {
            ensure!(
                !assumption_section,
                "assumption log combines assumptions with a closed context"
            );
            closed = true;
        } else if assumption_section
            && !line.starts_with(char::is_whitespace)
            && let Some((name, _)) = line.split_once(':')
        {
            let name = name.trim();
            text(name, "reported assumption")?;
            ensure!(
                name.split_whitespace().count() == 1,
                "invalid assumption report header: {name}"
            );
            ensure!(
                observed.insert(name),
                "duplicate reported assumption: {name}"
            );
        }
    }
    ensure!(
        expected == observed,
        "declared assumptions differ from the complete assumption report: expected {expected:?}, observed {observed:?}"
    );
    ensure!(
        if expected.is_empty() {
            closed && !assumption_section
        } else {
            assumption_section && !closed
        },
        "assumption log lacks a complete declaration-specific context result"
    );
    Ok(())
}

fn project_dependencies(
    root: &Path,
    proof_path: &str,
    modules: &BTreeMap<String, String>,
    visited: &mut BTreeSet<String>,
) -> Result<()> {
    if !visited.insert(proof_path.to_owned()) {
        return Ok(());
    }
    let source = fs::read_to_string(local_file(root, proof_path)?)?;
    for command in source_commands(&source)? {
        let words = command.split_whitespace().collect::<Vec<_>>();
        if words.first() == Some(&"Load") {
            bail!("kernel witness rejects dynamic Load dependencies in {proof_path}");
        }
        let (namespace, require_position) =
            if words.first() == Some(&"From") && words.get(2) == Some(&"Require") {
                let namespace = words.get(1).copied().unwrap_or_default();
                if !["OpenGororoba", "OpenGororobaVerified"]
                    .iter()
                    .any(|root| namespace == *root || namespace.starts_with(&format!("{root}.")))
                {
                    continue;
                }
                (Some(namespace), 2)
            } else if words.first() == Some(&"Require") {
                (None, 0)
            } else {
                continue;
            };
        let first_module = if matches!(words.get(require_position + 1), Some(&"Import" | &"Export"))
        {
            require_position + 2
        } else {
            require_position + 1
        };
        for name in words.iter().skip(first_module) {
            let logical = if let Some(namespace) = namespace {
                format!("{namespace}.{name}")
            } else if name.starts_with("OpenGororoba.") || name.starts_with("OpenGororobaVerified.")
            {
                (*name).to_owned()
            } else {
                let matches = modules
                    .keys()
                    .filter(|logical| logical.rsplit('.').next() == Some(*name))
                    .collect::<Vec<_>>();
                ensure!(
                    matches.len() <= 1,
                    "ambiguous unqualified project import: {name}"
                );
                if let Some(logical) = matches.first() {
                    (*logical).clone()
                } else {
                    continue;
                }
            };
            let dependency = modules
                .get(&logical)
                .with_context(|| format!("project import is unlisted: {logical}"))?;
            project_dependencies(root, dependency, modules, visited)?;
        }
    }
    Ok(())
}

pub(crate) fn validate_kernel_witness(
    root: &Path,
    witness: &TheoremKernelWitness,
    current_project: bool,
) -> Result<()> {
    ensure!(
        witness.schema_version == 1,
        "unsupported theorem kernel witness schema"
    );
    text(&witness.stable_id, "stable theorem identity")?;
    ensure!(
        witness.stable_id.starts_with("THM-"),
        "invalid stable theorem identity"
    );
    ensure!(
        witness.compile_exit_code == 0 && witness.kernel_exit_code == 0,
        "kernel promotion requires successful compiler and checker execution"
    );
    for (value, label) in [
        (&witness.compile_command, "compiler command"),
        (&witness.kernel_command, "kernel command"),
        (&witness.toolchain, "toolchain"),
    ] {
        text(value, label)?;
    }
    ensure!(
        matches!(
            witness.warning_policy.as_str(),
            "fatal_all" | "fatal_default" | "default_severity"
        ),
        "unsupported witness warning policy"
    );
    validate_execution_commands(witness)?;
    digest(&witness.project_sha256, "recorded proof project")?;
    if current_project {
        ensure!(
            file_sha256(&root.join("proofs/_RocqProject"))? == witness.project_sha256,
            "proof project prestate changed"
        );
    }
    let inventory =
        super::proof_inventory::load_proof_inventory(&root.join("proofs/_RocqProject"))?;
    let mut modules = BTreeMap::new();
    for entry in &inventory.source_entries {
        let relative = entry
            .path
            .as_str()
            .strip_prefix("proofs/")
            .context("invalid proof inventory root")?;
        let (source_root, name) = relative
            .split_once('/')
            .context("invalid proof source root")?;
        let namespace = if source_root == "theories" {
            "OpenGororoba"
        } else {
            "OpenGororobaVerified"
        };
        modules.insert(
            format!(
                "{namespace}.{}",
                name.trim_end_matches(".v").replace('/', ".")
            ),
            entry.path.to_string(),
        );
    }
    ensure!(
        inventory
            .source_entries
            .iter()
            .any(|entry| entry.path.as_str() == witness.proof_path),
        "kernel witness proof is outside the active source inventory"
    );
    let mut required = BTreeSet::new();
    project_dependencies(root, &witness.proof_path, &modules, &mut required)?;
    let mut observed = BTreeSet::new();
    for input in &witness.sources {
        ensure!(
            observed.insert(input.path.clone()),
            "duplicate kernel witness source: {}",
            input.path
        );
        ensure!(
            required.contains(&input.path),
            "kernel witness contains an unrelated source: {}",
            input.path
        );
        verify_file(root, input)?;
    }
    ensure!(
        required == observed,
        "kernel witness must bind the complete project dependency closure; required {required:?}; observed {observed:?}"
    );
    let compile_log = verify_file(root, &witness.compile_log)?;
    let kernel_log = verify_file(root, &witness.kernel_log)?;
    let assumption_log = verify_file(root, &witness.assumption_log)?;
    let proof_object = verify_file(root, &witness.proof_object)?;
    let output_paths = [
        &witness.compile_log.path,
        &witness.kernel_log.path,
        &witness.assumption_log.path,
        &witness.proof_object.path,
    ];
    ensure!(
        output_paths.into_iter().collect::<BTreeSet<_>>().len() == 4,
        "kernel witness output roles require distinct files"
    );
    ensure!(
        witness.proof_object.path.ends_with(".vo"),
        "kernel witness requires a retained proof object"
    );
    let source_name = Path::new(&witness.proof_path)
        .file_stem()
        .context("proof locator lacks a source stem")?;
    ensure!(
        Path::new(&witness.proof_object.path).file_stem() == Some(source_name),
        "retained proof object must name the witnessed source"
    );
    ensure!(
        fs::read(proof_object)?.starts_with(b"Coq!"),
        "kernel witness proof object lacks the Rocq object header"
    );
    for log in [&compile_log, &kernel_log, &assumption_log] {
        let contents = fs::read_to_string(log)?;
        ensure!(
            !contents.lines().any(
                |line| line.trim_start().starts_with("Error:") || line.contains("Fatal Error:")
            ),
            "kernel witness log contains an execution error"
        );
        if witness.warning_policy == "fatal_all" {
            ensure!(
                !contents
                    .lines()
                    .any(|line| line.trim_start().starts_with("Warning:")),
                "strict kernel witness log contains a warning"
            );
        }
    }
    ensure!(
        fs::read_to_string(kernel_log)?.contains("CONTEXT SUMMARY"),
        "kernel checker log lacks its context summary"
    );
    let declarations = source_commands(&fs::read_to_string(root.join(&witness.proof_path))?)?
        .into_iter()
        .filter_map(|command| {
            let words = command.split_whitespace().collect::<Vec<_>>();
            let declaration_position = usize::from(matches!(
                words.first(),
                Some(&"Local" | &"Global" | &"Polymorphic" | &"Monomorphic")
            ));
            if matches!(
                words.get(declaration_position),
                Some(
                    &"Theorem"
                        | &"Lemma"
                        | &"Corollary"
                        | &"Fact"
                        | &"Proposition"
                        | &"Definition"
                        | &"Example"
                )
            ) {
                words
                    .get(declaration_position + 1)
                    .map(|name| (name.trim_end_matches(':').to_owned(), words.join(" ")))
            } else {
                None
            }
        })
        .collect::<BTreeMap<_, _>>();
    ensure!(
        !witness.declarations.is_empty(),
        "kernel witness needs declaration-specific scope and assumptions"
    );
    let assumptions = fs::read_to_string(assumption_log)?;
    let mut names = BTreeSet::new();
    for declaration in &witness.declarations {
        text(&declaration.name, "declaration name")?;
        text(&declaration.statement, "declaration statement")?;
        ensure!(
            names.insert(&declaration.name),
            "kernel witness repeats declaration {}",
            declaration.name
        );
        ensure!(
            declarations.get(&declaration.name)
                == Some(
                    &declaration
                        .statement
                        .split_whitespace()
                        .collect::<Vec<_>>()
                        .join(" ")
                ),
            "kernel witness declaration statement differs from its source: {}",
            declaration.name
        );
        let reports = assumptions
            .split("Declaration: ")
            .skip(1)
            .filter_map(|block| {
                let (name, contents) = block.split_once('\n')?;
                (name.trim() == declaration.name).then_some(contents)
            })
            .collect::<Vec<_>>();
        ensure!(
            reports.len() == 1,
            "assumption log needs exactly one declaration label {}",
            declaration.name
        );
        validate_assumption_report(reports[0], &declaration.assumptions)?;
    }
    Ok(())
}

pub(crate) fn kernel_witness_matches(
    connection: &Connection,
    root: &Path,
    stable_id: &str,
    proof_path: &camino::Utf8Path,
) -> Result<bool> {
    let receipt: Option<(String, String)> = connection
        .query_row(
            "SELECT event.reason, event.spec_sha256 FROM theorem_identity_events event
         WHERE substr(event.binding_key,1,16) = 'kernel-evidence:'
           AND EXISTS (SELECT 1 FROM json_each(event.theorem_ids_json) WHERE value = ?1)
         ORDER BY event.id DESC LIMIT 1",
            [stable_id],
            |row| Ok((row.get(0)?, row.get(1)?)),
        )
        .optional()?;
    let Some((raw, spec_sha256)) = receipt else {
        return Ok(false);
    };
    let envelope: KernelEvidenceEnvelope =
        serde_json::from_str(&raw).context("parse retained kernel evidence event")?;
    ensure!(
        envelope.schema_version == 1 && sha256_hex(&envelope.raw_spec) == spec_sha256,
        "kernel evidence event envelope changed"
    );
    let specification = parse_theorem_kernel_evidence_spec(&envelope.raw_spec)?;
    ensure!(
        serde_json::to_value(&specification)? == serde_json::to_value(&envelope.specification)?,
        "kernel evidence event specification differs from its retained input"
    );
    let witness = &envelope.specification.witness;
    if witness.stable_id != stable_id || witness.proof_path != proof_path.as_str() {
        return Ok(false);
    }
    Ok(validate_kernel_witness(root, witness, true).is_ok())
}

impl ProvenanceStore {
    pub fn record_theorem_kernel_evidence(
        &mut self,
        root: &Path,
        specification: &TheoremKernelEvidenceSpec,
        raw: &str,
    ) -> Result<TheoremEvidenceMutationResult> {
        let validated = parse_theorem_kernel_evidence_spec(raw)?;
        ensure!(
            serde_json::to_value(&validated)? == serde_json::to_value(specification)?,
            "kernel specification differs from its retained input"
        );
        validate_kernel_witness(root, &specification.witness, true)?;
        let event_key = format!("kernel-evidence:{}", specification.evidence_key);
        let spec_sha256 = sha256_hex(raw);
        let transaction = self
            .conn
            .transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
        let before = read_state(&transaction, &specification.witness.stable_id)?;
        ensure!(
            before.proof_path == specification.witness.proof_path,
            "kernel witness identity has a different proof locator"
        );
        let existing: Option<(String, String)> = transaction
            .query_row(
                "SELECT spec_sha256,reason FROM theorem_identity_events WHERE binding_key=?1",
                [&event_key],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()?;
        if let Some((existing, envelope)) = existing {
            let envelope: KernelEvidenceEnvelope = serde_json::from_str(&envelope)?;
            ensure!(
                existing == spec_sha256 && before == envelope.after,
                "kernel evidence replay changed its specification or poststate"
            );
            transaction.commit()?;
            return Ok(TheoremEvidenceMutationResult {
                event_key,
                theorem_count: 1,
                source_only_count: 0,
                kernel_checked_count: 1,
                exact_replay: true,
            });
        }
        ensure!(
            sha256_hex(&before.kernel_result) == specification.expected_kernel_result_sha256
                && before.theorem_status == specification.expected_status,
            "kernel evidence prestate changed"
        );
        transaction.execute(
            "UPDATE theorems SET status=?2 WHERE id=?1",
            params![before.legacy_name, KERNEL_CHECKED],
        )?;
        let after = read_state(&transaction, &specification.witness.stable_id)?;
        let envelope = KernelEvidenceEnvelope {
            schema_version: 1,
            specification: specification.clone(),
            raw_spec: raw.to_owned(),
            before,
            after,
        };
        validate_kernel_witness(root, &specification.witness, true)?;
        transaction.execute("INSERT INTO theorem_identity_events(binding_key,spec_sha256,actor,reason,applied_at,theorem_ids_json,claim_ids_json) VALUES(?1,?2,?3,?4,?5,?6,'[]')", params![event_key,spec_sha256,specification.actor,serde_json::to_string(&envelope)?,specification.applied_at,serde_json::to_string(&[&specification.witness.stable_id])?])?;
        super::theorem_identity::validate_theorem_identities(&transaction, root)?;
        transaction.commit()?;
        Ok(TheoremEvidenceMutationResult {
            event_key,
            theorem_count: 1,
            source_only_count: 0,
            kernel_checked_count: 1,
            exact_replay: false,
        })
    }

    pub fn sync_theorem_inventory(
        &mut self,
        root: &Path,
        specification: &TheoremInventorySyncSpec,
        raw: &str,
    ) -> Result<TheoremEvidenceMutationResult> {
        let validated = parse_theorem_inventory_sync_spec(raw)?;
        ensure!(
            serde_json::to_value(&validated)? == serde_json::to_value(specification)?,
            "inventory specification differs from its retained input"
        );
        ensure!(
            file_sha256(&root.join("proofs/_RocqProject"))? == specification.project_sha256,
            "proof inventory project prestate changed"
        );
        let inventory =
            super::proof_inventory::load_proof_inventory(&root.join("proofs/_RocqProject"))?;
        let claims = self.list_claims()?;
        let event_key = format!("proof-inventory:{}", specification.sync_key);
        let spec_sha256 = sha256_hex(raw);
        let transaction = self
            .conn
            .transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
        let current_claims = {
            let mut query = transaction.prepare("SELECT id, statement, status, where_stated, last_verified, formal_proof, status_note, compat_toml_text FROM claims ORDER BY id")?;
            query
                .query_map([], |row| {
                    Ok(provenance_core::ClaimRecord {
                        id: row.get(0)?,
                        statement: row.get(1)?,
                        status: row.get(2)?,
                        where_stated: row.get(3)?,
                        last_verified: row.get(4)?,
                        formal_proof: row.get(5)?,
                        status_note: row.get(6)?,
                        compat_toml_text: row.get(7)?,
                    })
                })?
                .collect::<rusqlite::Result<Vec<_>>>()?
        };
        ensure!(
            serde_json::to_value(&claims)? == serde_json::to_value(&current_claims)?,
            "claim prestate changed during inventory synchronization"
        );
        let theorems = super::proof_inventory::load_theorems_from_inventory(
            &transaction,
            root,
            &inventory,
            &current_claims,
        )?;
        let before = all_theorem_states(&transaction)?;
        let existing: Option<(String, String)> = transaction
            .query_row(
                "SELECT spec_sha256,reason FROM theorem_identity_events WHERE binding_key=?1",
                [&event_key],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()?;
        if let Some((existing_hash, envelope)) = existing {
            let retained: serde_json::Value = serde_json::from_str(&envelope)?;
            ensure!(
                existing_hash == spec_sha256
                    && retained["after"] == serde_json::to_value(&before)?
                    && retained["projection_after"] == serde_json::to_value(&theorems)?,
                "inventory replay changed its specification, source evidence, or poststate"
            );
            transaction.commit()?;
            return Ok(inventory_result(event_key, &theorems, true));
        }
        let locators = theorems
            .iter()
            .map(|theorem| (theorem.legacy_name.as_str(), theorem.proof_path.as_str()))
            .collect::<BTreeMap<_, _>>();
        for state in &before {
            ensure!(
                locators.get(state.legacy_name.as_str()) == Some(&state.proof_path.as_str()),
                "registered proof locator is absent or changed: {}: {}",
                state.legacy_name,
                state.proof_path
            );
        }
        for theorem in &theorems {
            transaction.execute("INSERT INTO theorem_identities(stable_id,legacy_name,proof_path,identity_kind,source) VALUES(?1,?2,?3,?4,?5) ON CONFLICT(legacy_name) DO NOTHING", params![theorem.id,theorem.legacy_name,theorem.proof_path.as_str(),theorem.identity_kind,theorem.source])?;
            transaction.execute("INSERT INTO theorems(id,title,proof_path,status,linked_claim_ids_json,source) VALUES(?1,?2,?3,?4,?5,?6) ON CONFLICT(id) DO UPDATE SET status=excluded.status", params![theorem.legacy_name,theorem.title,theorem.proof_path.as_str(),theorem.status,serde_json::to_string(&theorem.linked_claim_ids)?,theorem.source])?;
            for claim in &theorem.linked_claim_ids {
                transaction.execute("INSERT OR IGNORE INTO theorem_claim_links(theorem_stable_id,claim_id,relation_kind) SELECT stable_id,?2,'formal_proposition' FROM theorem_identities WHERE legacy_name=?1", params![theorem.legacy_name,claim])?;
            }
        }
        super::theorem_identity::validate_theorem_identities(&transaction, root)?;
        ensure!(
            file_sha256(&root.join("proofs/_RocqProject"))? == specification.project_sha256,
            "proof inventory project changed during synchronization"
        );
        let final_inventory =
            super::proof_inventory::load_proof_inventory(&root.join("proofs/_RocqProject"))?;
        let final_theorems = super::proof_inventory::load_theorems_from_inventory(
            &transaction,
            root,
            &final_inventory,
            &current_claims,
        )?;
        ensure!(
            serde_json::to_value(&theorems)? == serde_json::to_value(&final_theorems)?,
            "source inventory or retained evidence changed during synchronization"
        );
        super::write_registry_snapshot(
            &transaction,
            root,
            "rocq_project",
            &root.join("proofs/_RocqProject"),
            &inventory.project_raw,
            &specification.applied_at,
        )?;
        let envelope = serde_json::to_string(
            &serde_json::json!({"schema":"theorem-source-inventory-v1","specification":specification,"raw_spec":raw,"before":before,"after":all_theorem_states(&transaction)?,"projection_after":theorems}),
        )?;
        transaction.execute("INSERT INTO theorem_identity_events(binding_key,spec_sha256,actor,reason,applied_at,theorem_ids_json,claim_ids_json) VALUES(?1,?2,?3,?4,?5,?6,'[]')", params![event_key,spec_sha256,specification.actor,envelope,specification.applied_at,serde_json::to_string(&theorems.iter().map(|theorem| &theorem.id).collect::<Vec<_>>())?])?;
        transaction.commit()?;
        Ok(inventory_result(event_key, &theorems, false))
    }
}

fn all_theorem_states(connection: &Connection) -> Result<Vec<TheoremLinkState>> {
    let identities = {
        let mut query =
            connection.prepare("SELECT stable_id FROM theorem_identities ORDER BY stable_id")?;
        query
            .query_map([], |row| row.get::<_, String>(0))?
            .collect::<rusqlite::Result<Vec<_>>>()?
    };
    identities
        .iter()
        .map(|stable_id| read_state(connection, stable_id))
        .collect()
}

fn inventory_result(
    event_key: String,
    theorems: &[provenance_core::TheoremRecord],
    exact_replay: bool,
) -> TheoremEvidenceMutationResult {
    TheoremEvidenceMutationResult {
        event_key,
        theorem_count: theorems.len(),
        source_only_count: theorems
            .iter()
            .filter(|theorem| theorem.status == SOURCE_ONLY)
            .count(),
        kernel_checked_count: theorems
            .iter()
            .filter(|theorem| theorem.status == KERNEL_CHECKED)
            .count(),
        exact_replay,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct Fixture {
        store: ProvenanceStore,
        root: PathBuf,
    }

    impl Fixture {
        fn new() -> Result<Self> {
            let mut connection = Connection::open_in_memory()?;
            connection.pragma_update(None, "foreign_keys", "ON")?;
            crate::migrations::migrations().to_latest(&mut connection)?;
            let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
            let root = std::env::temp_dir().join(format!(
                "gororoba-theorem-execution-{}-{nonce}",
                std::process::id()
            ));
            fs::create_dir_all(root.join("proofs/theories"))?;
            fs::create_dir_all(root.join("proofs/verified"))?;
            fs::create_dir(root.join("evidence"))?;
            fs::write(
                root.join("proofs/_RocqProject"),
                "-R theories OpenGororoba\n-R verified OpenGororobaVerified\ntheories/Prelude.v\nverified/C900_Test.v\n",
            )?;
            fs::write(
                root.join("proofs/theories/Prelude.v"),
                "Definition prerequisite : True := I.\n",
            )?;
            fs::write(
                root.join("proofs/verified/C900_Test.v"),
                "From OpenGororoba Require Import Prelude.\nTheorem fixture : True. Proof. exact I. Qed.\n",
            )?;
            fs::write(root.join("evidence/compile.log"), "")?;
            fs::write(root.join("evidence/kernel.log"), "CONTEXT SUMMARY\n")?;
            fs::write(
                root.join("evidence/assumptions.log"),
                "Declaration: fixture\nClosed under the global context\n",
            )?;
            fs::write(root.join("evidence/C900_Test.vo"), b"Coq!unit-fixture")?;
            connection.execute_batch(
                "INSERT INTO claims(id,statement,status,where_stated,last_verified,formal_proof,compat_toml_text)
                 VALUES('C-1','Actual formal scope','Verified','proofs/verified/C900_Test.v','2026-10-12','proofs/verified/C900_Test.v','');
                 INSERT INTO theorem_identities(stable_id,legacy_name,proof_path,identity_kind,assumptions,kernel_result,replay_command,falsifier,source)
                 VALUES('THM-TEST','C900_Test','proofs/verified/C900_Test.v','explicit_link','retained assumptions','retained kernel narrative','retained replay','retained falsifier','retained identity source');
                 INSERT INTO theorems(id,title,proof_path,status,linked_claim_ids_json,source)
                 VALUES('C900_Test','Retained title','proofs/verified/C900_Test.v','kernel_checked','[\"C-1\"]','retained theorem source');
                 INSERT INTO theorem_claim_links(theorem_stable_id,claim_id,relation_kind)
                 VALUES('THM-TEST','C-1','formal_proposition');",
            )?;
            Ok(Self {
                store: ProvenanceStore { conn: connection },
                root,
            })
        }

        fn file(&self, path: &str) -> Result<ProofFileDigest> {
            Ok(ProofFileDigest {
                path: path.to_owned(),
                sha256: file_sha256(&self.root.join(path))?,
            })
        }

        fn sync_spec(&self, key: &str) -> Result<TheoremInventorySyncSpec> {
            Ok(TheoremInventorySyncSpec {
                sync_key: key.to_owned(),
                actor: "test-actor".to_owned(),
                reason: "Bind the complete source inventory".to_owned(),
                applied_at: "2026-10-12T00:00:00Z".to_owned(),
                project_sha256: file_sha256(&self.root.join("proofs/_RocqProject"))?,
            })
        }

        fn sync(&mut self, key: &str) -> Result<TheoremEvidenceMutationResult> {
            let spec = self.sync_spec(key)?;
            let raw = toml::to_string(&spec)?;
            self.store.sync_theorem_inventory(&self.root, &spec, &raw)
        }

        fn witness(&self) -> Result<TheoremKernelEvidenceSpec> {
            let before = read_state(&self.store.conn, "THM-TEST")?;
            Ok(TheoremKernelEvidenceSpec {
                evidence_key:"fixture-evidence".to_owned(),actor:"test-actor".to_owned(),reason:"Retain checked declaration scope".to_owned(),applied_at:"2026-10-12T00:00:00Z".to_owned(),
                expected_kernel_result_sha256:sha256_hex(&before.kernel_result),expected_status:before.theorem_status,
                witness:TheoremKernelWitness {
                    schema_version:1,stable_id:"THM-TEST".to_owned(),proof_path:"proofs/verified/C900_Test.v".to_owned(),project_sha256:file_sha256(&self.root.join("proofs/_RocqProject"))?,
                    sources:vec![self.file("proofs/theories/Prelude.v")?,self.file("proofs/verified/C900_Test.v")?],
                    compile_log:self.file("evidence/compile.log")?,kernel_log:self.file("evidence/kernel.log")?,assumption_log:self.file("evidence/assumptions.log")?,proof_object:self.file("evidence/C900_Test.vo")?,
                    compile_command:"opam exec --switch rocq-9.1.1 -- rocq compile -q -w +all verified/C900_Test.v".to_owned(),kernel_command:"opam exec --switch rocq-9.1.1 -- rocq check OpenGororobaVerified.C900_Test".to_owned(),toolchain:"Rocq 9.1.1; OCaml 5.4.0".to_owned(),compile_exit_code:0,kernel_exit_code:0,warning_policy:"fatal_all".to_owned(),
                    declarations:vec![ProofDeclarationEvidence {name:"fixture".to_owned(),statement:"Theorem fixture : True".to_owned(),assumptions:Vec::new()}],
                },
            })
        }

        fn record(
            &mut self,
            spec: &TheoremKernelEvidenceSpec,
        ) -> Result<TheoremEvidenceMutationResult> {
            self.store
                .record_theorem_kernel_evidence(&self.root, spec, &toml::to_string(spec)?)
        }

        fn events(&self) -> Result<i64> {
            Ok(self.store.conn.query_row(
                "SELECT COUNT(*) FROM theorem_identity_events",
                [],
                |row| row.get(0),
            )?)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn inventory_sync_covers_both_roots_and_preserves_canonical_metadata() -> Result<()> {
        let mut fixture = Fixture::new()?;
        let before = read_state(&fixture.store.conn, "THM-TEST")?;
        let result = fixture.sync("source-inventory")?;
        assert_eq!(
            (
                result.theorem_count,
                result.source_only_count,
                result.kernel_checked_count
            ),
            (2, 2, 0)
        );
        let mut expected = before;
        expected.theorem_status = SOURCE_ONLY.to_owned();
        assert_eq!(read_state(&fixture.store.conn, "THM-TEST")?, expected);
        fixture
            .store
            .conn
            .query_row(
                "SELECT stable_id FROM theorem_identities WHERE legacy_name='Prelude'",
                [],
                |row| row.get::<_, String>(0),
            )
            .map(|stable_id| assert_eq!(stable_id, "THM-LEGACY-Prelude"))?;
        assert!(fixture.sync("source-inventory")?.exact_replay);
        assert_eq!(fixture.events()?, 1);
        assert_eq!(
            fixture
                .store
                .control_plane_counts()?
                .kernel_checked_claim_count,
            0
        );
        let raw: String = fixture.store.conn.query_row(
            "SELECT reason FROM theorem_identity_events",
            [],
            |row| row.get(0),
        )?;
        let envelope: serde_json::Value = serde_json::from_str(&raw)?;
        assert_eq!(
            envelope["before"][0]["kernel_result"],
            "retained kernel narrative"
        );
        assert_eq!(envelope["after"].as_array().unwrap().len(), 2);
        assert!(
            fixture
                .store
                .registry_snapshot("rocq_project")?
                .unwrap()
                .contains("theories/Prelude.v")
        );
        Ok(())
    }

    #[test]
    fn inventory_rejects_duplicates_collisions_missing_unlisted_and_traversal() -> Result<()> {
        let fixture = Fixture::new()?;
        let project = fixture.root.join("proofs/_RocqProject");
        let original = fs::read_to_string(&project)?;
        for invalid in [
            format!("{original}verified/C900_Test.v\n"),
            "theories/Prelude.v\nverified/Missing.v\n".to_owned(),
            "verified/C900_Test.v\n".to_owned(),
            "theories/../verified/C900_Test.v\n".to_owned(),
        ] {
            fs::write(&project, invalid)?;
            assert!(super::super::proof_inventory::load_proof_inventory(&project).is_err());
        }
        fs::write(
            fixture.root.join("proofs/verified/Prelude.v"),
            "Definition duplicate := True.\n",
        )?;
        fs::write(&project, format!("{original}verified/Prelude.v\n"))?;
        assert!(super::super::proof_inventory::load_proof_inventory(&project).is_err());
        Ok(())
    }

    #[test]
    fn inventory_sync_stale_guards_and_missing_registered_sources_rollback() -> Result<()> {
        let mut fixture = Fixture::new()?;
        let stale = fixture.sync_spec("stale")?;
        fs::write(
            fixture.root.join("proofs/_RocqProject"),
            "theories/Prelude.v\n",
        )?;
        assert!(
            fixture
                .store
                .sync_theorem_inventory(&fixture.root, &stale, &toml::to_string(&stale)?)
                .is_err()
        );
        fs::remove_file(fixture.root.join("proofs/verified/C900_Test.v"))?;
        assert!(fixture.sync("registered-source-removal").is_err());
        assert_eq!(fixture.events()?, 0);
        assert_eq!(
            read_state(&fixture.store.conn, "THM-TEST")?.theorem_status,
            KERNEL_CHECKED
        );
        Ok(())
    }

    #[test]
    fn inventory_source_only_numeric_stems_need_explicit_scope_before_promotion() -> Result<()> {
        let mut fixture = Fixture::new()?;
        fs::write(
            fixture.root.join("proofs/theories/C999_Unbound.v"),
            "Lemma unbound : True. exact I. Qed.\n",
        )?;
        let project = fixture.root.join("proofs/_RocqProject");
        fs::write(
            &project,
            format!("{}theories/C999_Unbound.v\n", fs::read_to_string(&project)?),
        )?;
        assert_eq!(fixture.sync("unbound-numeric")?.source_only_count, 3);
        let theorem = fixture
            .store
            .list_theorems()?
            .into_iter()
            .find(|theorem| theorem.legacy_name == "C999_Unbound")
            .unwrap();
        assert_eq!(theorem.identity_kind, "unresolved");
        assert!(theorem.linked_claim_ids.is_empty());
        Ok(())
    }

    #[test]
    fn kernel_receipt_promotes_without_overwriting_metadata_and_replays_exactly() -> Result<()> {
        let mut fixture = Fixture::new()?;
        fixture.sync("initial")?;
        let before = read_state(&fixture.store.conn, "THM-TEST")?;
        let spec = fixture.witness()?;
        assert!(!fixture.record(&spec)?.exact_replay);
        let mut expected = before.clone();
        expected.theorem_status = KERNEL_CHECKED.to_owned();
        assert_eq!(read_state(&fixture.store.conn, "THM-TEST")?, expected);
        assert!(fixture.record(&spec)?.exact_replay);
        assert_eq!(fixture.events()?, 2);
        assert_eq!(
            fixture
                .store
                .control_plane_counts()?
                .kernel_checked_claim_count,
            1
        );
        fixture.store.conn.execute("UPDATE theorem_identities SET kernel_result='Updated explanation' WHERE stable_id='THM-TEST'",[])?;
        assert_eq!(
            fixture
                .sync("metadata-after-evidence")?
                .kernel_checked_count,
            1
        );
        assert!(fixture.record(&spec).is_err());
        assert_eq!(fixture.events()?, 3);
        let raw:String = fixture.store.conn.query_row("SELECT reason FROM theorem_identity_events WHERE binding_key='kernel-evidence:fixture-evidence'",[],|row| row.get(0))?;
        let envelope: KernelEvidenceEnvelope = serde_json::from_str(&raw)?;
        assert_eq!(envelope.before, before);
        assert_eq!(envelope.after, expected);
        Ok(())
    }

    #[test]
    fn kernel_receipt_source_dependency_and_artifact_mutations_demote_projection() -> Result<()> {
        for path in [
            "proofs/verified/C900_Test.v",
            "proofs/theories/Prelude.v",
            "evidence/C900_Test.vo",
            "evidence/kernel.log",
        ] {
            let mut fixture = Fixture::new()?;
            fixture.sync("initial")?;
            fixture.record(&fixture.witness()?)?;
            let original = fs::read(fixture.root.join(path))?;
            let mut changed = original;
            changed.extend_from_slice(b"\n(* changed input *)\n");
            fs::write(fixture.root.join(path), changed)?;
            assert_eq!(
                fixture.sync("changed-input")?.kernel_checked_count,
                0,
                "{path}"
            );
            assert_eq!(
                read_state(&fixture.store.conn, "THM-TEST")?.kernel_result,
                "retained kernel narrative"
            );
            assert_eq!(fixture.events()?, 3);
        }
        Ok(())
    }

    #[test]
    fn kernel_receipt_project_edits_demote_and_old_sync_replay_rejects_changed_evidence()
    -> Result<()> {
        let mut fixture = Fixture::new()?;
        fixture.sync("initial")?;
        fixture.record(&fixture.witness()?)?;
        fixture.sync("checked-inventory")?;
        let old_spec = fixture.sync_spec("checked-inventory")?;
        let project = fixture.root.join("proofs/_RocqProject");
        fs::write(
            &project,
            format!(
                "{}# changed namespace or warning-policy input\n",
                fs::read_to_string(&project)?
            ),
        )?;
        assert!(
            fixture
                .store
                .sync_theorem_inventory(&fixture.root, &old_spec, &toml::to_string(&old_spec)?)
                .is_err()
        );
        assert_eq!(fixture.sync("changed-project")?.kernel_checked_count, 0);
        assert_eq!(fixture.events()?, 4);
        Ok(())
    }

    #[test]
    fn kernel_receipt_rejects_incomplete_closure_nonzero_exit_false_statement_and_policy()
    -> Result<()> {
        for mutation in 0..16 {
            let mut fixture = Fixture::new()?;
            fixture.sync("initial")?;
            let before = read_state(&fixture.store.conn, "THM-TEST")?;
            let mut spec = fixture.witness()?;
            match mutation {
                0 => {
                    spec.witness.sources.remove(0);
                }
                1 => spec.witness.compile_exit_code = 1,
                2 => spec.witness.kernel_exit_code = 1,
                3 => spec.witness.declarations[0].statement = "Theorem fixture : False".to_owned(),
                4 => spec.witness.warning_policy = "unknown".to_owned(),
                5 => spec.witness.compile_command.push_str(" -vos"),
                6 => spec.witness.kernel_command.push_str(" -admit X"),
                7 => spec.witness.sources.push(spec.witness.sources[0].clone()),
                8 => spec.expected_kernel_result_sha256 = sha256_hex("wrong prestate"),
                9 => spec.witness.declarations[0]
                    .assumptions
                    .push("Hidden.Axiom".to_owned()),
                10 => spec.witness.kernel_log = spec.witness.compile_log.clone(),
                11 => {
                    fs::write(
                        fixture.root.join("evidence/C900_Test.vo"),
                        b"invalid object",
                    )?;
                    spec.witness.proof_object = fixture.file("evidence/C900_Test.vo")?;
                }
                12 => spec.witness.compile_command = "true verified/C900_Test.v -w +all".to_owned(),
                13 => {
                    spec.witness.compile_command =
                        spec.witness.compile_command.replace("+all", "@all")
                }
                14 => spec.witness.compile_command.push_str(" -w none"),
                15 => spec.witness.compile_command.push_str(" -w"),
                _ => unreachable!(),
            }
            assert!(fixture.record(&spec).is_err(), "mutation {mutation}");
            assert_eq!(read_state(&fixture.store.conn, "THM-TEST")?, before);
            assert_eq!(fixture.events()?, 1);
        }
        Ok(())
    }

    #[test]
    fn kernel_receipt_rejects_hidden_assumptions_warnings_and_checker_failure_logs() -> Result<()> {
        for (path, contents) in [
            (
                "evidence/assumptions.log",
                "Declaration: fixture\nAxioms:\nHidden.Axiom : True\nClosed under the global context\n",
            ),
            (
                "evidence/assumptions.log",
                "Declaration: fixture\nAxioms:\nVisible.Axiom : True\nHidden.Axiom : True\n",
            ),
            ("evidence/compile.log", "Warning: fatal diagnostic\n"),
            (
                "evidence/kernel.log",
                "Error: checker failure\nCONTEXT SUMMARY\n",
            ),
        ] {
            let mut fixture = Fixture::new()?;
            fixture.sync("initial")?;
            fs::write(fixture.root.join(path), contents)?;
            let mut spec = fixture.witness()?;
            if contents.contains("Visible.Axiom") {
                spec.witness.declarations[0].assumptions = vec!["Visible.Axiom".to_owned()];
            }
            assert!(fixture.record(&spec).is_err(), "{contents}");
            assert_eq!(fixture.events()?, 1);
        }
        Ok(())
    }

    #[test]
    fn assumption_scope_and_fatal_default_are_explicit() -> Result<()> {
        let mut fixture = Fixture::new()?;
        fixture.sync("initial")?;
        fs::write(
            fixture.root.join("evidence/assumptions.log"),
            "Declaration: fixture\nRocq < Axioms:\nVisible.Axiom :\n  forall predicate : Prop, predicate -> predicate\n",
        )?;
        let mut spec = fixture.witness()?;
        spec.witness.declarations[0].assumptions = vec!["Visible.Axiom".to_owned()];
        spec.witness.warning_policy = "fatal_default".to_owned();
        spec.witness.compile_command = spec.witness.compile_command.replace("+all", "+default");
        fixture.record(&spec)?;
        assert_eq!(
            fixture.sync("checked-default-policy")?.kernel_checked_count,
            1
        );
        Ok(())
    }

    #[test]
    fn source_parser_preserves_qualified_names_and_nested_comments() -> Result<()> {
        assert_eq!(
            source_commands(
                "(* outer (* nested *) *) From OpenGororoba Require Import Foo.Bar.\nTheorem foo (* rationale *) : True.(* note *) Proof. exact I. Qed."
            )?,
            [
                "From OpenGororoba Require Import Foo.Bar",
                "Theorem foo   : True",
                "Proof",
                "exact I",
                "Qed"
            ]
        );
        assert!(source_commands("(* unterminated").is_err());
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn inventory_rejects_a_symlinked_source_root() -> Result<()> {
        let fixture = Fixture::new()?;
        fs::rename(
            fixture.root.join("proofs/theories"),
            fixture.root.join("retained-theories"),
        )?;
        std::os::unix::fs::symlink(
            fixture.root.join("retained-theories"),
            fixture.root.join("proofs/theories"),
        )?;
        assert!(
            super::super::proof_inventory::load_proof_inventory(
                &fixture.root.join("proofs/_RocqProject")
            )
            .is_err()
        );
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn inventory_and_evidence_reject_symlink_paths() -> Result<()> {
        let fixture = Fixture::new()?;
        std::os::unix::fs::symlink(
            fixture.root.join("evidence/compile.log"),
            fixture.root.join("proofs/theories/Symlink.v"),
        )?;
        assert!(
            super::super::proof_inventory::load_proof_inventory(
                &fixture.root.join("proofs/_RocqProject")
            )
            .is_err()
        );
        std::os::unix::fs::symlink(
            fixture.root.join("evidence"),
            fixture.root.join("linked-evidence"),
        )?;
        assert!(local_file(&fixture.root, "linked-evidence/compile.log").is_err());
        Ok(())
    }
}
