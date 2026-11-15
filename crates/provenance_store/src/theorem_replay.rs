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

/// The Flocq object list of the opam switch that runs the replay producer.
/// The bytes equal `ci/flocq-manifest.json` of gororoba-math, whose sha256 is
/// `4f881f92f000f60bfb3be28b8a8dbf8d55ad240702e02442bd5c8d52a2c5f903`, at
/// commit `ecf95ce5f1a11a9d20d79adea802e443dfd25e4a`. A replay that lists
/// Flocq objects admits only this list.
const PINNED_FLOCQ_MANIFEST: &str = include_str!("../fixtures/flocq_manifest/rocq-9.3.json");
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
    /// no Flocq object bytes, so ingest checks each digest's form, requires the
    /// list to equal [`PINNED_FLOCQ_MANIFEST`] and records it verbatim.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    flocq_objects: Vec<ProofFileDigest>,
    compilation: Vec<CommandEvidence>,
    checker: CommandEvidence,
    assumptions: CommandEvidence,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FlocqManifest {
    schema_version: u32,
    switch: String,
    packages: BTreeMap<String, String>,
    flocq_objects: Vec<ProofFileDigest>,
}

fn pinned_flocq_manifest() -> Result<FlocqManifest> {
    let manifest: FlocqManifest =
        serde_json::from_str(PINNED_FLOCQ_MANIFEST).context("parse pinned Flocq manifest")?;
    ensure!(
        manifest.schema_version == 1
            && !manifest.switch.is_empty()
            && !manifest.packages.is_empty(),
        "unsupported pinned Flocq manifest identity"
    );
    validate_flocq_objects(&manifest.flocq_objects)?;
    Ok(manifest)
}

/// Checks a Flocq object list for its core object, sorted unique `.vo` paths
/// below `external/Flocq/` and lowercase hexadecimal digests.
fn validate_flocq_objects(objects: &[ProofFileDigest]) -> Result<()> {
    ensure!(
        objects
            .iter()
            .any(|object| object.path == "external/Flocq/Core/Core.vo"),
        "Flocq replay lacks its core object"
    );
    let mut previous = "";
    for object in objects {
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
    Ok(())
}

/// Requires two sorted object lists to be equal, and names the first path at
/// which they differ: a changed digest, an object the manifest lacks, or a
/// manifest object the replay lacks.
fn compare_flocq_objects(recorded: &[ProofFileDigest], manifest: &[ProofFileDigest]) -> Result<()> {
    for index in 0..recorded.len().max(manifest.len()) {
        match (recorded.get(index), manifest.get(index)) {
            (Some(object), Some(pinned)) if object.path == pinned.path => ensure!(
                object.sha256 == pinned.sha256,
                "Flocq replay object {} differs from the pinned manifest: digest {} against {}",
                object.path,
                object.sha256,
                pinned.sha256
            ),
            (Some(object), Some(pinned)) if object.path < pinned.path => anyhow::bail!(
                "Flocq replay object {} is absent from the pinned manifest",
                object.path
            ),
            (Some(object), None) => anyhow::bail!(
                "Flocq replay object {} is absent from the pinned manifest",
                object.path
            ),
            (_, Some(pinned)) => anyhow::bail!(
                "pinned manifest object {} is absent from the Flocq replay",
                pinned.path
            ),
            (None, None) => unreachable!("the index is below the longer list length"),
        }
    }
    Ok(())
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
            validate_flocq_objects(&self.flocq_objects)?;
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
/// closure, a Flocq object list present exactly when a source imports Flocq
/// and equal to the pinned manifest of the producer's switch, and retained compile, kernel and assumption logs equal to the output of the
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
    if !evidence.flocq_objects.is_empty() {
        compare_flocq_objects(
            &evidence.flocq_objects,
            &pinned_flocq_manifest()?.flocq_objects,
        )?;
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    const FLOCQ_EVIDENCE: &str =
        include_str!("../fixtures/kernel_replay/flocq/C900_Test.evidence.json");

    fn fixture_objects() -> Vec<ProofFileDigest> {
        let evidence: serde_json::Value =
            serde_json::from_str(FLOCQ_EVIDENCE).expect("flocq fixture evidence parses");
        serde_json::from_value(evidence["flocq_objects"].clone())
            .expect("flocq fixture lists objects")
    }

    fn message(recorded: &[ProofFileDigest], manifest: &[ProofFileDigest]) -> String {
        format!(
            "{:#}",
            compare_flocq_objects(recorded, manifest).expect_err("the lists differ")
        )
    }

    #[test]
    fn pinned_manifest_is_well_formed_and_names_the_producer_switch() -> Result<()> {
        let manifest = pinned_flocq_manifest()?;
        assert_eq!(manifest.switch, "rocq-9.3");
        assert_eq!(
            manifest
                .packages
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["coq-flocq", "rocq-core"]
        );
        assert!(manifest.flocq_objects.len() > 1);
        Ok(())
    }

    #[test]
    fn the_flocq_fixture_evidence_equals_the_pinned_manifest() -> Result<()> {
        compare_flocq_objects(&fixture_objects(), &pinned_flocq_manifest()?.flocq_objects)
    }

    #[test]
    fn a_changed_digest_is_rejected_at_its_path() -> Result<()> {
        let manifest = pinned_flocq_manifest()?.flocq_objects;
        let mut recorded = fixture_objects();
        let index = recorded.len() / 2;
        let flipped = if recorded[index].sha256.starts_with('0') {
            '1'
        } else {
            '0'
        };
        recorded[index]
            .sha256
            .replace_range(..1, &flipped.to_string());
        let text = message(&recorded, &manifest);
        assert!(text.contains(&recorded[index].path), "{text}");
        assert!(text.contains("differs from the pinned manifest"), "{text}");
        Ok(())
    }

    #[test]
    fn a_removed_object_is_rejected_at_its_path() -> Result<()> {
        let manifest = pinned_flocq_manifest()?.flocq_objects;
        let mut recorded = fixture_objects();
        let removed = recorded.remove(recorded.len() / 2);
        let text = message(&recorded, &manifest);
        assert!(text.contains(&removed.path), "{text}");
        assert!(text.contains("absent from the Flocq replay"), "{text}");
        let mut last = fixture_objects();
        let dropped = last.pop().context("fixture lists objects")?;
        let text = message(&last, &manifest);
        assert!(text.contains(&dropped.path), "{text}");
        Ok(())
    }

    #[test]
    fn an_added_object_is_rejected_at_its_path() -> Result<()> {
        let manifest = pinned_flocq_manifest()?.flocq_objects;
        let mut recorded = fixture_objects();
        let added = ProofFileDigest {
            path: "external/Flocq/Core/Extra.vo".to_owned(),
            sha256: "0".repeat(64),
        };
        recorded.push(added.clone());
        recorded.sort_by(|left, right| left.path.cmp(&right.path));
        validate_flocq_objects(&recorded)?;
        let text = message(&recorded, &manifest);
        assert!(text.contains(&added.path), "{text}");
        assert!(text.contains("absent from the pinned manifest"), "{text}");
        let mut trailing = fixture_objects();
        let last = ProofFileDigest {
            path: "external/Flocq/Zzz.vo".to_owned(),
            sha256: "1".repeat(64),
        };
        trailing.push(last.clone());
        let text = message(&trailing, &manifest);
        assert!(text.contains(&last.path), "{text}");
        Ok(())
    }
}
