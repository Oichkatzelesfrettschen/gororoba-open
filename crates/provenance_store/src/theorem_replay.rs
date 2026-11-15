//! Kernel replay evidence: a gororoba-math producer compiles and checks the
//! proof closure, and this module validates the evidence file it wrote against
//! the witness and the proof tree. Nothing here runs Rocq.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use anyhow::{Context, Result, ensure};
use serde::{Deserialize, Serialize};

use super::{EvidenceRoots, ProofFileDigest, TheoremKernelWitness};

const TOOLCHAIN: &str = "Rocq 9.3.0; OCaml 5.5.1";
const RETAINED_TOOLCHAINS: [&str; 3] = [
    "Rocq 9.1.1; OCaml 5.4.0",
    "Rocq 9.2; OCaml 5.5.0",
    TOOLCHAIN,
];

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct CommandEvidence {
    arguments: Vec<String>,
    exit_code: i32,
    stdout: String,
    stderr: String,
}

impl CommandEvidence {
    fn log(&self) -> String {
        format!("{}\n{}", self.stdout, self.stderr)
    }

    /// The bytes a retained log file holds: standard output, then standard error.
    fn output(&self) -> String {
        format!("{}{}", self.stdout, self.stderr)
    }

    fn validate(&self, arguments: Vec<String>) -> Result<()> {
        ensure!(
            self.arguments == arguments && self.exit_code == 0,
            "retained Rocq replay command differs from its fixed execution contract"
        );
        let log = self.log();
        ensure!(
            !log.lines().any(
                |line| line.trim_start().starts_with("Error:") || line.contains("Fatal Error:")
            ),
            "retained Rocq replay contains an execution error"
        );
        ensure!(
            !log.lines()
                .any(|line| line.trim_start().starts_with("Warning:")),
            "trusted Rocq replay rejects warning output"
        );
        for prefix in ["/home/", "/root/", "/tmp/", "/run/user/", "/var/tmp/"] {
            ensure!(
                !log.contains(prefix),
                "Rocq replay output contains a local absolute path"
            );
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct KernelReplayEvidence {
    schema_version: u32,
    toolchain: String,
    project_sha256: String,
    sources: Vec<ProofFileDigest>,
    proof_object_sha256: String,
    /// Flocq object digests as the producer reports them. The repository holds
    /// no Flocq object bytes, so ingest checks each digest's form and records
    /// the list verbatim; no digest is compared with a file.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    flocq_objects: Vec<ProofFileDigest>,
    compilation: Vec<CommandEvidence>,
    checker: CommandEvidence,
    assumptions: CommandEvidence,
}

fn relative_source(path: &str) -> Result<&str> {
    path.strip_prefix("proofs/")
        .context("replay source must belong to proofs/")
}

fn logical_module(path: &str) -> Result<String> {
    let source = relative_source(path)?;
    let (source_root, stem) = source
        .split_once('/')
        .context("replay source lacks its root")?;
    let namespace = match source_root {
        "theories" => "OpenGororoba",
        "verified" => "OpenGororobaVerified",
        _ => anyhow::bail!("unsupported replay source root"),
    };
    let stem = stem
        .strip_suffix(".v")
        .context("replay source needs .v suffix")?;
    Ok(format!("{namespace}.{}", stem.replace('/', ".")))
}

fn warning_argument(witness: &TheoremKernelWitness) -> Result<&str> {
    match witness.warning_policy.as_str() {
        "fatal_all" => Ok("+all"),
        "fatal_default" => Ok("+default"),
        "default_severity" => anyhow::bail!("trusted replay requires a fatal warning policy"),
        _ => anyhow::bail!("unsupported replay warning policy"),
    }
}

fn compiler_arguments(source: &str, witness: &TheoremKernelWitness) -> Result<Vec<String>> {
    Ok([
        "compile",
        "-q",
        "-w",
        warning_argument(witness)?,
        "-R",
        "theories",
        "OpenGororoba",
        "-R",
        "verified",
        "OpenGororobaVerified",
        source,
    ]
    .into_iter()
    .map(str::to_owned)
    .collect())
}

fn checker_arguments(witness: &TheoremKernelWitness) -> Result<Vec<String>> {
    Ok([
        "check",
        "-silent",
        "-o",
        "-R",
        "theories",
        "OpenGororoba",
        "-R",
        "verified",
        "OpenGororobaVerified",
        &logical_module(&witness.proof_path)?,
    ]
    .into_iter()
    .map(str::to_owned)
    .collect())
}

fn external_arguments(mut arguments: Vec<String>, flocq: bool) -> Vec<String> {
    if flocq {
        let target = arguments
            .pop()
            .expect("fixed Rocq arguments include a target");
        arguments.extend(["-R", "external/Flocq", "Flocq"].map(str::to_owned));
        arguments.push(target);
    }
    arguments
}

fn uses_flocq(roots: EvidenceRoots<'_>, witness: &TheoremKernelWitness) -> Result<bool> {
    for source in &witness.sources {
        let contents = fs::read_to_string(super::verify_file(roots, source)?)?;
        for command in super::source_commands(&contents)? {
            let words = command.split_whitespace().collect::<Vec<_>>();
            if (words.first() == Some(&"From")
                && words.get(2) == Some(&"Require")
                && words.get(1).is_some_and(|namespace| {
                    *namespace == "Flocq" || namespace.starts_with("Flocq.")
                }))
                || (words.first() == Some(&"Require")
                    && words
                        .iter()
                        .skip(1)
                        .any(|module| module.starts_with("Flocq.")))
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

impl KernelReplayEvidence {
    pub(super) fn validate(&self, witness: &TheoremKernelWitness) -> Result<()> {
        ensure!(
            self.schema_version == 1
                && RETAINED_TOOLCHAINS.contains(&self.toolchain.as_str())
                && self.toolchain == witness.toolchain,
            "unsupported trusted Rocq replay identity"
        );
        ensure!(
            self.project_sha256 == witness.project_sha256
                && self.sources == witness.sources
                && self.proof_object_sha256 == witness.proof_object.sha256,
            "trusted Rocq replay differs from witnessed source or object bytes"
        );
        let mut compiled = BTreeSet::new();
        let flocq = !self.flocq_objects.is_empty();
        if flocq {
            ensure!(
                self.flocq_objects
                    .iter()
                    .any(|object| object.path == "external/Flocq/Core/Core.vo"),
                "Flocq replay lacks its core object"
            );
            let mut previous = "";
            for object in &self.flocq_objects {
                let relative = object
                    .path
                    .strip_prefix("external/Flocq/")
                    .context("invalid Flocq replay object root")?;
                ensure!(
                    object.path.as_str() > previous
                        && relative.ends_with(".vo")
                        && Path::new(relative)
                            .components()
                            .all(|component| matches!(component, std::path::Component::Normal(_))),
                    "invalid or repeated Flocq replay object path"
                );
                // The digest is checked for its form (64 lowercase hexadecimal
                // characters) and recorded as the producer reports it; this
                // repository holds no Flocq object bytes to compare it with.
                ensure!(
                    object.sha256.len() == 64
                        && object
                            .sha256
                            .bytes()
                            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
                    "invalid Flocq object digest"
                );
                previous = &object.path;
            }
        }
        for command in &self.compilation {
            let source = command
                .arguments
                .last()
                .context("replay compilation lacks a source")?;
            ensure!(
                compiled.insert(format!("proofs/{source}")),
                "replay repeats a compiled source"
            );
            command.validate(external_arguments(
                compiler_arguments(source, witness)?,
                flocq,
            ))?;
        }
        ensure!(
            compiled
                == witness
                    .sources
                    .iter()
                    .map(|source| source.path.clone())
                    .collect(),
            "replay compilation differs from complete source closure"
        );
        self.checker
            .validate(external_arguments(checker_arguments(witness)?, flocq))?;
        ensure!(
            self.checker.log().contains("CONTEXT SUMMARY"),
            "trusted checker replay lacks its context summary"
        );
        self.assumptions.validate(external_arguments(
            compiler_arguments("KernelReceiptAssumptions.v", witness)?,
            flocq,
        ))?;
        let log = self.assumptions.log();
        let reports = super::labeled_assumption_reports(&log)?;
        ensure!(
            reports.keys().cloned().collect::<BTreeSet<_>>()
                == witness
                    .declarations
                    .iter()
                    .map(|declaration| declaration.name.clone())
                    .collect(),
            "trusted assumption replay has a different declaration set"
        );
        for declaration in &witness.declarations {
            super::validate_assumption_report(
                reports[&declaration.name],
                &declaration.assumptions,
            )?;
        }
        Ok(())
    }
}

/// Parses the evidence file of the gororoba-math producer and admits it for
/// `witness`. The producer ran this module's fixed argument vectors over the
/// witnessed closure; admission needs no Rocq, because the evidence binds to
/// bytes this repository retains. It requires the pinned toolchain and a fatal
/// warning policy, the evidence contract of [`KernelReplayEvidence::validate`],
/// the witnessed source, log and object bytes (re-hashed through
/// `validate_kernel_witness`, which also gives the proof object digest the
/// evidence records), a compilation order equal to the dependency order of the
/// closure, a Flocq object list present exactly when a source imports Flocq,
/// and retained compile, kernel and assumption logs equal to the output of the
/// matching commands.
pub(super) fn ingest(
    roots: EvidenceRoots<'_>,
    witness: &TheoremKernelWitness,
    raw: &str,
) -> Result<KernelReplayEvidence> {
    ensure!(
        witness.toolchain == TOOLCHAIN,
        "witness toolchain differs from the pinned replay toolchain"
    );
    warning_argument(witness)?;
    let evidence: KernelReplayEvidence =
        serde_json::from_str(raw).context("parse kernel replay evidence")?;
    evidence.validate(witness)?;
    super::validate_kernel_witness(roots, witness, true)?;
    let inventory = crate::proof_inventory::load_proof_inventory(roots.tree)?;
    let modules = inventory
        .source_entries
        .iter()
        .map(|entry| Ok((logical_module(entry.path.as_str())?, entry.path.to_string())))
        .collect::<Result<BTreeMap<_, _>>>()?;
    let mut ordered = Vec::new();
    super::project_dependencies(
        roots,
        &witness.proof_path,
        &modules,
        &mut BTreeSet::new(),
        &mut ordered,
    )?;
    let compiled = evidence
        .compilation
        .iter()
        .map(|command| {
            command
                .arguments
                .last()
                .map(|source| format!("proofs/{source}"))
                .context("replay compilation lacks a source")
        })
        .collect::<Result<Vec<_>>>()?;
    ensure!(
        compiled == ordered,
        "replay compilation is not the dependency order of the source closure"
    );
    ensure!(
        uses_flocq(roots, witness)? == !evidence.flocq_objects.is_empty(),
        "Flocq replay objects disagree with the witnessed sources"
    );
    let target = ordered
        .iter()
        .position(|source| *source == witness.proof_path)
        .and_then(|position| evidence.compilation.get(position))
        .context("replay lacks the compilation of the witnessed source")?;
    for (log, produced, role) in [
        (&witness.compile_log, target.output(), "compile"),
        (&witness.kernel_log, evidence.checker.output(), "kernel"),
        (
            &witness.assumption_log,
            evidence.assumptions.output(),
            "assumption",
        ),
    ] {
        ensure!(
            fs::read_to_string(roots.locate(&log.path)?)? == produced,
            "retained {role} log differs from the replay evidence"
        );
    }
    Ok(evidence)
}
#[cfg(test)]
pub(super) fn fixture_evidence(witness: &TheoremKernelWitness) -> Result<KernelReplayEvidence> {
    let command = |arguments, stdout: String| CommandEvidence {
        arguments,
        exit_code: 0,
        stdout,
        stderr: String::new(),
    };
    let compilation = witness
        .sources
        .iter()
        .map(|source| {
            Ok(command(
                compiler_arguments(relative_source(&source.path)?, witness)?,
                String::new(),
            ))
        })
        .collect::<Result<_>>()?;
    let mut stdout = String::new();
    for declaration in &witness.declarations {
        stdout.push_str(&format!("Declaration: {}\n", declaration.name));
        if declaration.assumptions.is_empty() {
            stdout.push_str("Closed under the global context\n");
        } else {
            stdout.push_str("Axioms:\n");
            for assumption in &declaration.assumptions {
                stdout.push_str(&format!("{assumption} : True\n"));
            }
        }
    }
    Ok(KernelReplayEvidence {
        schema_version: 1,
        toolchain: TOOLCHAIN.to_owned(),
        project_sha256: witness.project_sha256.clone(),
        sources: witness.sources.clone(),
        proof_object_sha256: witness.proof_object.sha256.clone(),
        flocq_objects: Vec::new(),
        compilation,
        checker: command(checker_arguments(witness)?, "CONTEXT SUMMARY\n".to_owned()),
        assumptions: command(
            compiler_arguments("KernelReceiptAssumptions.v", witness)?,
            stdout,
        ),
    })
}
