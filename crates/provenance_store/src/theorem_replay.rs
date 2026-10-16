//! Trusted record-time Rocq execution; later admission checks only retained bytes.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::{Context, Result, ensure};
use serde::{Deserialize, Serialize};

use super::{ProofFileDigest, TheoremKernelWitness};

const TOOLCHAIN: &str = "Rocq 9.3.0; OCaml 5.5.1";
const RETAINED_TOOLCHAINS: [&str; 2] = ["Rocq 9.2; OCaml 5.5.0", TOOLCHAIN];
const VERSION: &str = "The Rocq Prover, version 9.3.0\ncompiled with OCaml 5.5.1";

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

fn uses_flocq(root: &Path, witness: &TheoremKernelWitness) -> Result<bool> {
    for source in &witness.sources {
        let contents = fs::read_to_string(super::verify_file(root, source)?)?;
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

fn configured_flocq_root(root: &Path) -> Result<PathBuf> {
    let configured = if let Some(path) = std::env::var_os("FLOCQ_ROOT") {
        PathBuf::from(path)
    } else if let Some(prefix) = std::env::var_os("OPAM_SWITCH_PREFIX") {
        PathBuf::from(prefix).join("lib/coq/user-contrib/Flocq")
    } else {
        let output = Command::new("opam")
            .args(["var", "lib"])
            .output()
            .context("resolve active opam Flocq library")?;
        ensure!(
            output.status.success() && output.stderr.is_empty(),
            "cannot resolve active opam Flocq library"
        );
        let library = String::from_utf8(output.stdout)?;
        ensure!(
            !library.trim().is_empty(),
            "active opam library path is empty"
        );
        PathBuf::from(library.trim()).join("coq/user-contrib/Flocq")
    };
    let configured = if configured.is_absolute() {
        configured
    } else {
        root.join("proofs").join(configured)
    };
    ensure!(
        configured.join("Core/Core.vo").is_file(),
        "configured Flocq Core.vo is missing"
    );
    Ok(configured)
}

fn copy_flocq_objects(
    source: &Path,
    destination: &Path,
    relative: &Path,
    objects: &mut Vec<ProofFileDigest>,
) -> Result<()> {
    fs::create_dir_all(destination.join(relative))?;
    for entry in fs::read_dir(source.join(relative))? {
        let entry = entry?;
        let kind = entry.file_type()?;
        ensure!(
            !kind.is_symlink(),
            "Flocq replay rejects symbolic library entries"
        );
        let relative = relative.join(entry.file_name());
        if kind.is_dir() {
            copy_flocq_objects(source, destination, &relative, objects)?;
        } else if kind.is_file()
            && relative
                .extension()
                .is_some_and(|extension| extension == "vo")
        {
            let path = source.join(&relative);
            let digest = super::file_sha256(&path)?;
            fs::copy(&path, destination.join(&relative))?;
            ensure!(
                super::file_sha256(&destination.join(&relative))? == digest,
                "Flocq object changed during copy"
            );
            objects.push(ProofFileDigest {
                path: format!(
                    "external/Flocq/{}",
                    relative
                        .to_str()
                        .context("Flocq object path must be UTF-8")?
                ),
                sha256: digest,
            });
        }
    }
    Ok(())
}

fn prepare_flocq(
    root: &Path,
    directory: &Path,
    witness: &TheoremKernelWitness,
) -> Result<Vec<ProofFileDigest>> {
    if !uses_flocq(root, witness)? {
        return Ok(Vec::new());
    }
    let mut objects = Vec::new();
    copy_flocq_objects(
        &configured_flocq_root(root)?,
        &directory.join("external/Flocq"),
        Path::new(""),
        &mut objects,
    )?;
    objects.sort_by(|left, right| left.path.cmp(&right.path));
    Ok(objects)
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

struct ScratchDirectory(PathBuf);

impl ScratchDirectory {
    fn new() -> Result<Self> {
        for attempt in 0..16 {
            let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
            let path = std::env::temp_dir().join(format!(
                "gororoba-rocq-replay-{}-{nonce}-{attempt}",
                std::process::id()
            ));
            let mut builder = fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                builder.mode(0o700);
            }
            match builder.create(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(error).context("create private Rocq replay scratch directory");
                }
            }
        }
        anyhow::bail!("cannot allocate a fresh Rocq replay scratch directory")
    }
}

impl Drop for ScratchDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn trusted_program() -> Result<PathBuf> {
    let search = std::env::var_os("PATH").context("trusted Rocq replay needs a host PATH")?;
    for directory in std::env::split_paths(&search) {
        let candidate = directory.join("rocq");
        if !candidate.is_file() {
            continue;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if fs::metadata(&candidate)?.permissions().mode() & 0o111 == 0 {
                continue;
            }
        }
        let candidate = std::path::absolute(candidate)?;
        let output = Command::new(&candidate)
            .arg("--version")
            .output()
            .context("execute host-selected Rocq version probe")?;
        ensure!(
            output.status.success()
                && output.stderr.is_empty()
                && String::from_utf8(output.stdout)?.trim() == VERSION,
            "trusted replay requires Rocq 9.3.0 compiled with OCaml 5.5.1"
        );
        return Ok(candidate);
    }
    anyhow::bail!("trusted Rocq replay requires rocq in the host PATH/opam switch")
}

fn run(program: &Path, directory: &Path, arguments: Vec<String>) -> Result<CommandEvidence> {
    let output = Command::new(program)
        .current_dir(directory)
        .env_remove("COQPATH")
        .env_remove("ROCQPATH")
        .args(&arguments)
        .output()
        .context("execute trusted Rocq replay")?;
    let evidence = CommandEvidence {
        arguments,
        exit_code: output.status.code().unwrap_or(-1),
        stdout: String::from_utf8(output.stdout).context("Rocq replay stdout must be UTF-8")?,
        stderr: String::from_utf8(output.stderr).context("Rocq replay stderr must be UTF-8")?,
    };
    ensure!(
        output.status.success(),
        "trusted Rocq replay failed with exit {}: {}",
        evidence.exit_code,
        evidence.log()
    );
    Ok(evidence)
}

pub(super) fn execute(root: &Path, witness: &TheoremKernelWitness) -> Result<KernelReplayEvidence> {
    ensure!(
        witness.toolchain == TOOLCHAIN,
        "witness toolchain differs from the trusted pinned replay toolchain"
    );
    warning_argument(witness)?;
    let program = trusted_program()?;
    let scratch = ScratchDirectory::new()?;
    fs::create_dir(scratch.0.join("theories"))?;
    fs::create_dir(scratch.0.join("verified"))?;
    let inventory =
        crate::proof_inventory::load_proof_inventory(&root.join("proofs/_RocqProject"))?;
    let modules = inventory
        .source_entries
        .iter()
        .map(|entry| Ok((logical_module(entry.path.as_str())?, entry.path.to_string())))
        .collect::<Result<BTreeMap<_, _>>>()?;
    let mut ordered = Vec::new();
    super::project_dependencies(
        root,
        &witness.proof_path,
        &modules,
        &mut BTreeSet::new(),
        &mut ordered,
    )?;
    for source in &witness.sources {
        let contents = fs::read(super::verify_file(root, source)?)?;
        let destination = scratch.0.join(relative_source(&source.path)?);
        fs::create_dir_all(
            destination
                .parent()
                .context("replay source lacks a parent")?,
        )?;
        fs::write(&destination, contents)?;
        ensure!(
            super::file_sha256(&destination)? == source.sha256,
            "source changed while preparing replay: {}",
            source.path
        );
    }
    let flocq_objects = prepare_flocq(root, &scratch.0, witness)?;
    let flocq = !flocq_objects.is_empty();
    let mut compilation = Vec::new();
    for source in ordered {
        compilation.push(run(
            &program,
            &scratch.0,
            external_arguments(
                compiler_arguments(relative_source(&source)?, witness)?,
                flocq,
            ),
        )?);
    }
    let object = scratch
        .0
        .join(relative_source(&witness.proof_path)?)
        .with_extension("vo");
    let proof_object_sha256 = super::file_sha256(&object)?;
    ensure!(
        proof_object_sha256 == witness.proof_object.sha256,
        "retained proof object differs from genuine source-closure compilation"
    );
    let checker = run(
        &program,
        &scratch.0,
        external_arguments(checker_arguments(witness)?, flocq),
    )?;
    let logical = logical_module(&witness.proof_path)?;
    let mut query = format!("Require Import {logical}.\n");
    for declaration in &witness.declarations {
        query.push_str(&format!("Goal True.\nProof.\n  idtac \"Declaration: {}\".\n  exact I.\nQed.\nPrint Assumptions {logical}.{}.\n", declaration.name, declaration.name));
    }
    fs::write(scratch.0.join("KernelReceiptAssumptions.v"), query)?;
    let assumptions = run(
        &program,
        &scratch.0,
        external_arguments(
            compiler_arguments("KernelReceiptAssumptions.v", witness)?,
            flocq,
        ),
    )?;
    for object in &flocq_objects {
        ensure!(
            super::file_sha256(&scratch.0.join(&object.path))? == object.sha256,
            "Flocq replay object changed during execution"
        );
    }
    let evidence = KernelReplayEvidence {
        schema_version: 1,
        toolchain: TOOLCHAIN.to_owned(),
        project_sha256: witness.project_sha256.clone(),
        sources: witness.sources.clone(),
        proof_object_sha256,
        flocq_objects,
        compilation,
        checker,
        assumptions,
    };
    evidence.validate(witness)?;
    super::validate_kernel_witness(root, witness, true)?;
    Ok(evidence)
}

#[cfg(test)]
pub(super) fn genuine_fixture_artifacts(root: &Path, witness: &TheoremKernelWitness) -> Result<()> {
    let program = trusted_program()?;
    let directory = root.join("proofs");
    let flocq = !prepare_flocq(root, &directory, witness)?.is_empty();
    let mut target_log = String::new();
    for source in &witness.sources {
        let evidence = run(
            &program,
            &directory,
            external_arguments(
                compiler_arguments(relative_source(&source.path)?, witness)?,
                flocq,
            ),
        )?;
        if source.path == witness.proof_path {
            target_log = evidence.log();
        }
    }
    fs::write(root.join("evidence/compile.log"), target_log)?;
    fs::copy(
        directory
            .join(relative_source(&witness.proof_path)?)
            .with_extension("vo"),
        root.join("evidence/C900_Test.vo"),
    )?;
    let checked = run(
        &program,
        &directory,
        external_arguments(checker_arguments(witness)?, flocq),
    )?;
    fs::write(root.join("evidence/kernel.log"), checked.log())?;
    let logical = logical_module(&witness.proof_path)?;
    fs::write(
        directory.join("KernelReceiptAssumptions.v"),
        format!(
            "Require Import {logical}.\nGoal True. Proof. idtac \"Declaration: fixture\". exact I. Qed.\nPrint Assumptions {logical}.fixture.\n"
        ),
    )?;
    let assumptions = run(
        &program,
        &directory,
        external_arguments(
            compiler_arguments("KernelReceiptAssumptions.v", witness)?,
            flocq,
        ),
    )?;
    fs::write(root.join("evidence/assumptions.log"), assumptions.log())?;
    Ok(())
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
