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

const TOOLCHAIN: &str = "Rocq 9.1.1; OCaml 5.4.0";
const VERSION: &str = "The Rocq Prover, version 9.1.1\ncompiled with OCaml 5.4.0";

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

impl KernelReplayEvidence {
    pub(super) fn validate(&self, witness: &TheoremKernelWitness) -> Result<()> {
        ensure!(
            self.schema_version == 1
                && self.toolchain == TOOLCHAIN
                && witness.toolchain == TOOLCHAIN,
            "unsupported trusted Rocq replay identity"
        );
        ensure!(
            self.project_sha256 == witness.project_sha256
                && self.sources == witness.sources
                && self.proof_object_sha256 == witness.proof_object.sha256,
            "trusted Rocq replay differs from witnessed source or object bytes"
        );
        let mut compiled = BTreeSet::new();
        for command in &self.compilation {
            let source = command
                .arguments
                .last()
                .context("replay compilation lacks a source")?;
            ensure!(
                compiled.insert(format!("proofs/{source}")),
                "replay repeats a compiled source"
            );
            command.validate(compiler_arguments(source, witness)?)?;
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
        self.checker.validate(checker_arguments(witness)?)?;
        ensure!(
            self.checker.log().contains("CONTEXT SUMMARY"),
            "trusted checker replay lacks its context summary"
        );
        self.assumptions
            .validate(compiler_arguments("KernelReceiptAssumptions.v", witness)?)?;
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
            "trusted replay requires Rocq 9.1.1 compiled with OCaml 5.4.0"
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
    let mut compilation = Vec::new();
    for source in ordered {
        compilation.push(run(
            &program,
            &scratch.0,
            compiler_arguments(relative_source(&source)?, witness)?,
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
    let checker = run(&program, &scratch.0, checker_arguments(witness)?)?;
    let logical = logical_module(&witness.proof_path)?;
    let mut query = format!("Require Import {logical}.\n");
    for declaration in &witness.declarations {
        query.push_str(&format!("Goal True.\n  idtac \"Declaration: {}\".\n  exact I.\nQed.\nPrint Assumptions {logical}.{}.\n", declaration.name, declaration.name));
    }
    fs::write(scratch.0.join("KernelReceiptAssumptions.v"), query)?;
    let assumptions = run(
        &program,
        &scratch.0,
        compiler_arguments("KernelReceiptAssumptions.v", witness)?,
    )?;
    let evidence = KernelReplayEvidence {
        schema_version: 1,
        toolchain: TOOLCHAIN.to_owned(),
        project_sha256: witness.project_sha256.clone(),
        sources: witness.sources.clone(),
        proof_object_sha256,
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
    let mut target_log = String::new();
    for source in &witness.sources {
        let evidence = run(
            &program,
            &directory,
            compiler_arguments(relative_source(&source.path)?, witness)?,
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
    let checked = run(&program, &directory, checker_arguments(witness)?)?;
    fs::write(root.join("evidence/kernel.log"), checked.log())?;
    let logical = logical_module(&witness.proof_path)?;
    fs::write(
        directory.join("KernelReceiptAssumptions.v"),
        format!(
            "Require Import {logical}.\nGoal True. idtac \"Declaration: fixture\". exact I. Qed.\nPrint Assumptions {logical}.fixture.\n"
        ),
    )?;
    let assumptions = run(
        &program,
        &directory,
        compiler_arguments("KernelReceiptAssumptions.v", witness)?,
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
        compilation,
        checker: command(checker_arguments(witness)?, "CONTEXT SUMMARY\n".to_owned()),
        assumptions: command(
            compiler_arguments("KernelReceiptAssumptions.v", witness)?,
            stdout,
        ),
    })
}
