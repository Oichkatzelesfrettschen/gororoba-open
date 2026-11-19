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

/// The Flocq object lists of the producers of the replay evidence, one entry
/// per producer. The bytes equal `ci/flocq-manifest.json` of gororoba-math
/// (schema_version 2), whose sha256 is
/// `01cbaf6d07f088508defb5d23910a920df06aabeaaedead3044038007f1ced35`, at
/// commit `e69fa46421d8024cf5fae68b6f8ff4c184b7b364`. A `.vo` records the md5
/// of each OCaml plugin it loads, and those plugin bytes depend on the install
/// prefix and the native toolchain of the producer (measured: the same opam
/// export gave different Flocq object bytes on a hosted runner, first at
/// `Calc/Bracket.vo`). A replay that lists Flocq objects names its producer in
/// `flocq_producer` and admits only that producer's list, so evidence from a
/// build of the switch that no entry records is rejected.
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
    /// list to equal the entry of [`PINNED_FLOCQ_MANIFEST`] that
    /// `flocq_producer` names and records it verbatim.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    flocq_objects: Vec<ProofFileDigest>,
    /// The manifest entry of the producer whose switch supplied
    /// `flocq_objects`; present exactly when that list is non-empty.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    flocq_producer: Option<String>,
    compilation: Vec<CommandEvidence>,
    checker: CommandEvidence,
    assumptions: CommandEvidence,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FlocqManifest {
    schema_version: u32,
    switch: String,
    producers: Vec<FlocqProducer>,
}

/// One producer of the manifest: its name, the toolchain that built its
/// switch, its package versions and its Flocq object list.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FlocqProducer {
    name: String,
    toolchain: FlocqToolchain,
    packages: BTreeMap<String, String>,
    flocq_objects: Vec<ProofFileDigest>,
}

/// The toolchain identity of a producer. The md5 of `ltac_plugin.cmxs` is the
/// digest every Flocq `.vo` of the producer inherits; the three versions
/// describe the build.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FlocqToolchain {
    gcc: String,
    binutils: String,
    glibc: String,
    ltac_plugin_md5: String,
}

fn lowercase_hexadecimal(text: &str, length: usize) -> bool {
    text.len() == length
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn pinned_flocq_manifest() -> Result<FlocqManifest> {
    parse_flocq_manifest(PINNED_FLOCQ_MANIFEST)
}

/// Parses a manifest document and checks its identity: schema version 2, sorted
/// unique producer names, unique plugin digests and well-formed object lists.
fn parse_flocq_manifest(text: &str) -> Result<FlocqManifest> {
    let manifest: FlocqManifest =
        serde_json::from_str(text).context("parse pinned Flocq manifest")?;
    ensure!(
        manifest.schema_version == 2
            && !manifest.switch.is_empty()
            && !manifest.producers.is_empty(),
        "unsupported pinned Flocq manifest identity"
    );
    let mut previous = "";
    let mut plugins = BTreeSet::new();
    for producer in &manifest.producers {
        ensure!(
            producer.name.as_str() > previous
                && !producer.name.is_empty()
                && producer.name.bytes().all(|byte| {
                    byte.is_ascii_lowercase()
                        || byte.is_ascii_digit()
                        || byte == b'.'
                        || byte == b'-'
                }),
            "invalid or repeated pinned Flocq producer name {}",
            producer.name
        );
        let toolchain = &producer.toolchain;
        ensure!(
            ![&toolchain.gcc, &toolchain.binutils, &toolchain.glibc]
                .iter()
                .any(|version| version.is_empty())
                && lowercase_hexadecimal(&toolchain.ltac_plugin_md5, 32)
                && plugins.insert(toolchain.ltac_plugin_md5.as_str())
                && !producer.packages.is_empty(),
            "invalid toolchain identity of pinned Flocq producer {}",
            producer.name
        );
        validate_flocq_objects(&producer.flocq_objects)?;
        previous = &producer.name;
    }
    Ok(manifest)
}

/// Requires the recorded Flocq objects to equal the pinned entry of the
/// producer that the evidence names. A missing name, a name no entry carries
/// and a list that differs from the named entry each reject the evidence.
fn check_flocq_producer(
    manifest: &FlocqManifest,
    producer: Option<&str>,
    objects: &[ProofFileDigest],
) -> Result<()> {
    let name = producer.context("Flocq replay objects lack their flocq_producer")?;
    let entry = manifest
        .producers
        .iter()
        .find(|entry| entry.name == name)
        .with_context(|| format!("Flocq producer {name} is not in the pinned manifest"))?;
    compare_flocq_objects(objects, &entry.flocq_objects)
        .with_context(|| format!("Flocq producer {name}"))
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
            lowercase_hexadecimal(&object.sha256, 64),
            "invalid Flocq object digest for {}",
            object.path
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

/// The control flags of Rocq 9.3.0 (`control_flag` of its vernacular grammar),
/// each with the number of argument tokens it takes: `Redirect` a string,
/// `Timeout` a natural, `AllocLimit` a natural and `Mw` or `kw`. `Profile`
/// takes an optional string.
const CONTROL_FLAGS: [(&str, usize); 8] = [
    ("Time", 0),
    ("Instructions", 0),
    ("Profile", 0),
    ("Redirect", 1),
    ("Timeout", 1),
    ("AllocLimit", 2),
    ("Fail", 0),
    ("Succeed", 0),
];

/// The legacy attributes of Rocq 9.3.0 (`legacy_attr` of its vernacular
/// grammar).
const LEGACY_ATTRIBUTES: [&str; 8] = [
    "Local",
    "Global",
    "Polymorphic",
    "Monomorphic",
    "Cumulative",
    "NonCumulative",
    "Private",
    "Program",
];

/// A token of one command: an attribute (`#[` to its matching `]`), a string
/// literal, a parenthesis, or a word, a run of characters that holds no
/// whitespace, quote or parenthesis and ends before `#[`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Token<'a> {
    Attribute,
    String,
    Open,
    Close,
    Word(&'a str),
}

/// The index after the quote that closes a string whose text starts at
/// `cursor`; a doubled quote inside a Rocq string literal stands for one
/// quote character. The delimiters are ASCII, so a byte scan finds them.
fn string_end(command: &str, mut cursor: usize) -> Option<usize> {
    let bytes = command.as_bytes();
    while cursor < bytes.len() {
        if bytes[cursor] == b'"' {
            if bytes.get(cursor + 1) == Some(&b'"') {
                cursor += 2;
                continue;
            }
            return Some(cursor + 1);
        }
        cursor += 1;
    }
    None
}

/// The index after the bracket that closes an attribute whose text starts at
/// `cursor`. Brackets nest, and a bracket inside a string literal of the
/// attribute is text.
fn attribute_end(command: &str, mut cursor: usize) -> Option<usize> {
    let bytes = command.as_bytes();
    let mut depth = 1usize;
    while cursor < bytes.len() {
        match bytes[cursor] {
            b'"' => {
                cursor = string_end(command, cursor + 1)?;
                continue;
            }
            b'[' => depth += 1,
            b']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(cursor + 1);
                }
            }
            _ => {}
        }
        cursor += 1;
    }
    None
}

/// The tokens of one command, or `None` when an attribute or a string is
/// unterminated.
fn command_tokens(command: &str) -> Option<Vec<Token<'_>>> {
    let mut tokens = Vec::new();
    let mut cursor = 0;
    while let Some(character) = command[cursor..].chars().next() {
        if character.is_whitespace() {
            cursor += character.len_utf8();
        } else if command[cursor..].starts_with("#[") {
            cursor = attribute_end(command, cursor + 2)?;
            tokens.push(Token::Attribute);
        } else if character == '"' {
            cursor = string_end(command, cursor + 1)?;
            tokens.push(Token::String);
        } else if character == '(' || character == ')' {
            tokens.push(if character == '(' {
                Token::Open
            } else {
                Token::Close
            });
            cursor += 1;
        } else {
            let start = cursor;
            while let Some(next) = command[cursor..].chars().next() {
                if next.is_whitespace()
                    || matches!(next, '"' | '(' | ')')
                    || command[cursor..].starts_with("#[")
                {
                    break;
                }
                cursor += next.len_utf8();
            }
            tokens.push(Token::Word(&command[start..cursor]));
        }
    }
    Some(tokens)
}

fn is_flocq(name: &str) -> bool {
    name == "Flocq" || name.starts_with("Flocq.")
}

/// The module names among the arguments of `Require`. Rocq 9.3 reads
/// `Require [Import | Export [-](CATEGORIES)] MODULE[(NAMES)]...`
/// (`export_token` and `filtered_import` of its vernacular grammar), so the
/// names are the words outside parentheses after a leading `Import` or
/// `Export`, other than the category negation `-`.
fn module_words<'a>(mut arguments: &[Token<'a>]) -> Vec<&'a str> {
    if let [Token::Word("Import" | "Export"), tail @ ..] = arguments {
        arguments = tail;
    }
    let mut depth = 0usize;
    let mut words = Vec::new();
    for token in arguments {
        match *token {
            Token::Open => depth += 1,
            Token::Close => depth = depth.saturating_sub(1),
            Token::Word(word) if depth == 0 && word != "-" => words.push(word),
            _ => {}
        }
    }
    words
}

/// Whether one command imports Flocq. The rule is that of
/// `command_imports_flocq` of the gororoba-math kernel replay evidence
/// producer, and the Flocq import corpus that the tests pin holds the cases
/// both answer. A run of control flags (`CONTROL_FLAGS`, each with its
/// argument tokens and `Profile` with an optional string), attributes and
/// legacy attributes (`LEGACY_ATTRIBUTES`) is skipped in any order; Rocq 9.3
/// reads them in the order flags, attributes, legacy attributes and rejects
/// the other orders. `Fail` is skipped like the others: a command under
/// `Fail` may load Flocq before it fails. Then `From NAMESPACE Require`
/// imports Flocq when `NAMESPACE` is `Flocq` or starts with `Flocq.`, since
/// Rocq resolves the modules under `NAMESPACE`, and a bare `Require` imports
/// Flocq when a module word is `Flocq` or starts with `Flocq.`. A command
/// that names no module, or whose attribute or string is unterminated,
/// imports nothing.
fn command_imports_flocq(command: &str) -> bool {
    imports_flocq_under(command, &CONTROL_FLAGS, &LEGACY_ATTRIBUTES)
}

/// `command_imports_flocq` over the given prefix tables, which a test
/// shortens by one entry.
fn imports_flocq_under(
    command: &str,
    control_flags: &[(&str, usize)],
    legacy_attributes: &[&str],
) -> bool {
    let Some(tokens) = command_tokens(command) else {
        return false;
    };
    let mut position = 0;
    while let Some(token) = tokens.get(position) {
        match *token {
            Token::Attribute => position += 1,
            Token::Word(word) if legacy_attributes.contains(&word) => position += 1,
            Token::Word(word) => {
                let Some(&(_, arguments)) = control_flags.iter().find(|(flag, _)| *flag == word)
                else {
                    break;
                };
                position += 1 + arguments;
                if word == "Profile" && tokens.get(position) == Some(&Token::String) {
                    position += 1;
                }
            }
            _ => break,
        }
    }
    match tokens.get(position..).unwrap_or_default() {
        [
            Token::Word("From"),
            Token::Word(namespace),
            Token::Word("Require"),
            arguments @ ..,
        ] => is_flocq(namespace) && !module_words(arguments).is_empty(),
        [Token::Word("Require"), arguments @ ..] => {
            module_words(arguments).into_iter().any(is_flocq)
        }
        _ => false,
    }
}

fn uses_flocq(roots: EvidenceRoots<'_>, witness: &TheoremKernelWitness) -> Result<bool> {
    for source in &witness.sources {
        let contents = fs::read_to_string(super::verify_file(roots, source)?)?;
        for command in super::source_commands(&contents)? {
            if command_imports_flocq(&command) {
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
        ensure!(
            flocq || self.flocq_producer.is_none(),
            "a Flocq producer is named without Flocq replay objects"
        );
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
///
/// A non-empty Flocq list must also name its producer in `flocq_producer` and
/// equal that producer's entry of [`PINNED_FLOCQ_MANIFEST`]. The object bytes
/// depend on the install prefix and the native toolchain of the producer
/// (measured: a hosted runner that built the same export produced different
/// bytes, first at `Calc/Bracket.vo`), so evidence from a build of the switch
/// that no entry records is rejected here. The comparison applies to a new
/// event key at admission; a stored envelope keeps the contract it was
/// admitted under.
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
        check_flocq_producer(
            &pinned_flocq_manifest()?,
            evidence.flocq_producer.as_deref(),
            &evidence.flocq_objects,
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
        flocq_producer: None,
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

    /// The Flocq import corpus of gororoba-math (`flocq-import-corpus.tsv`),
    /// whose sha256 is
    /// `5b5cdfb485701a0dcd6289ff4fc74c290f51afe963f956f9e66e453c14afa36b`,
    /// first at commit `66af7e4d38f5fcb6dd4f52ea12aec4a403f27c35`. The
    /// calibration of the gororoba-math evidence producer reads the same
    /// corpus. `ci/flocq_import_corpus.pin` names the gororoba-math commit whose
    /// corpus this copy equals, apart from `ci/gororoba_math.pin`, because the
    /// retained kernel receipts bind the proof tree of that pin.
    /// `the_vendored_flocq_import_corpus_equals_that_of_gororoba_math` compares
    /// this copy with the corpus file `FLOCQ_IMPORT_CORPUS` names, so a rule
    /// change in either repository fails a test until both read one corpus
    /// again.
    const FLOCQ_IMPORT_CORPUS: &str =
        include_str!("../fixtures/flocq_import_corpus/flocq-import-corpus.tsv");
    const FLOCQ_IMPORT_CORPUS_SHA256: &str =
        "5b5cdfb485701a0dcd6289ff4fc74c290f51afe963f956f9e66e453c14afa36b";

    /// The (command, expected answer) rows of the corpus: a header line, then
    /// one tab-separated row per command with `true` or `false`.
    fn flocq_import_corpus() -> Result<Vec<(&'static str, bool)>> {
        let body = FLOCQ_IMPORT_CORPUS
            .strip_prefix("command\timports_flocq\n")
            .context("the Flocq import corpus lacks its header")?
            .strip_suffix('\n')
            .context("the Flocq import corpus lacks its final newline")?;
        let rows = body
            .split('\n')
            .enumerate()
            .map(|(index, line)| {
                let (command, expected) = line
                    .split_once('\t')
                    .with_context(|| format!("corpus row {} has no tab", index + 2))?;
                ensure!(
                    !command.is_empty() && !expected.contains('\t'),
                    "corpus row {} is malformed",
                    index + 2
                );
                let expected = match expected {
                    "true" => true,
                    "false" => false,
                    _ => anyhow::bail!("corpus row {} has no boolean answer", index + 2),
                };
                Ok((command, expected))
            })
            .collect::<Result<Vec<_>>>()?;
        let commands = rows
            .iter()
            .map(|(command, _)| command)
            .collect::<BTreeSet<_>>();
        ensure!(
            commands.len() == rows.len(),
            "the Flocq import corpus repeats a command"
        );
        Ok(rows)
    }

    /// Environment variable naming the corpus file of the gororoba-math commit
    /// that `ci/flocq_import_corpus.pin` names.
    const FLOCQ_IMPORT_CORPUS_ENV: &str = "FLOCQ_IMPORT_CORPUS";

    #[test]
    #[ignore = "reads the gororoba-math Flocq import corpus; set FLOCQ_IMPORT_CORPUS and run with --include-ignored"]
    fn the_vendored_flocq_import_corpus_equals_that_of_gororoba_math() -> Result<()> {
        let path = std::env::var_os(FLOCQ_IMPORT_CORPUS_ENV)
            .filter(|value| !value.is_empty())
            .with_context(|| {
                format!(
                    "{FLOCQ_IMPORT_CORPUS_ENV} is unset; set it to the flocq-import-corpus.tsv \
                     of the gororoba-math commit that ci/flocq_import_corpus.pin names"
                )
            })?;
        let path = Path::new(&path);
        let corpus = fs::read_to_string(path).with_context(|| {
            format!(
                "read the Flocq import corpus {} that {FLOCQ_IMPORT_CORPUS_ENV} names",
                path.display()
            )
        })?;
        ensure!(
            corpus == FLOCQ_IMPORT_CORPUS,
            "the vendored Flocq import corpus (sha256 {}) differs from the gororoba-math corpus \
             that {FLOCQ_IMPORT_CORPUS_ENV} names (sha256 {})",
            crate::sha256_hex(FLOCQ_IMPORT_CORPUS),
            crate::sha256_hex(&corpus)
        );
        Ok(())
    }

    #[test]
    fn the_flocq_import_corpus_has_its_pinned_digest() {
        assert_eq!(
            crate::sha256_hex(FLOCQ_IMPORT_CORPUS),
            FLOCQ_IMPORT_CORPUS_SHA256
        );
    }

    #[test]
    fn flocq_imports_follow_the_pinned_corpus() -> Result<()> {
        let corpus = flocq_import_corpus()?;
        assert!(!corpus.is_empty());
        for (command, expected) in corpus {
            assert_eq!(command_imports_flocq(command), expected, "{command}");
            // The source reader yields the row as one command, or refuses the
            // source, which is a refused run and imports nothing.
            match crate::theorem_execution::source_commands(&format!("{command}.")) {
                Ok(commands) => assert_eq!(commands, [command], "{command}"),
                Err(_) => assert!(!expected, "{command}"),
            }
        }
        Ok(())
    }

    #[test]
    fn the_corpus_rejects_a_rule_without_any_one_prefix() -> Result<()> {
        let corpus = flocq_import_corpus()?;
        let answers_corpus = |flags: &[(&str, usize)], legacy: &[&str]| {
            corpus
                .iter()
                .all(|(command, expected)| imports_flocq_under(command, flags, legacy) == *expected)
        };
        assert!(answers_corpus(&CONTROL_FLAGS, &LEGACY_ATTRIBUTES));
        for (flag, _) in CONTROL_FLAGS {
            let flags = CONTROL_FLAGS
                .into_iter()
                .filter(|(name, _)| *name != flag)
                .collect::<Vec<_>>();
            assert!(!answers_corpus(&flags, &LEGACY_ATTRIBUTES), "{flag}");
        }
        for attribute in LEGACY_ATTRIBUTES {
            let legacy = LEGACY_ATTRIBUTES
                .into_iter()
                .filter(|name| *name != attribute)
                .collect::<Vec<_>>();
            assert!(!answers_corpus(&CONTROL_FLAGS, &legacy), "{attribute}");
        }
        Ok(())
    }

    #[test]
    fn a_malformed_digest_is_rejected_at_its_path() {
        let mut objects = fixture_objects();
        let index = objects.len() / 2;
        objects[index].sha256 = "Z".repeat(64);
        let text = format!(
            "{:#}",
            validate_flocq_objects(&objects).expect_err("digest is malformed")
        );
        assert!(text.contains(&objects[index].path), "{text}");
    }

    const PRODUCER_A: &str = "cachyos-gcc-16.2.1";
    const PRODUCER_B: &str = "ubuntu-26.04-gcc-15.2.0";

    fn producer_objects(name: &str) -> Result<Vec<ProofFileDigest>> {
        pinned_flocq_manifest()?
            .producers
            .into_iter()
            .find(|producer| producer.name == name)
            .map(|producer| producer.flocq_objects)
            .with_context(|| format!("the pinned manifest lacks producer {name}"))
    }

    fn rejection(producer: Option<&str>, objects: &[ProofFileDigest]) -> Result<String> {
        let error = check_flocq_producer(&pinned_flocq_manifest()?, producer, objects)
            .expect_err("the evidence is rejected");
        Ok(format!("{error:#}"))
    }

    #[test]
    fn pinned_manifest_is_well_formed_and_names_both_producers() -> Result<()> {
        let manifest = pinned_flocq_manifest()?;
        assert_eq!(manifest.switch, "rocq-9.3");
        assert_eq!(
            manifest
                .producers
                .iter()
                .map(|producer| producer.name.as_str())
                .collect::<Vec<_>>(),
            [PRODUCER_A, PRODUCER_B]
        );
        for producer in &manifest.producers {
            assert_eq!(
                producer
                    .packages
                    .keys()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
                ["coq-flocq", "rocq-core"]
            );
            assert!(producer.flocq_objects.len() > 1);
        }
        assert_eq!(
            manifest
                .producers
                .iter()
                .map(|producer| producer.toolchain.ltac_plugin_md5.as_str())
                .collect::<Vec<_>>(),
            [
                "1014006bc3627f54b6f91150cf1d341b",
                "5a8480da6ef6fbb19e3d4a62ab3c0e6f"
            ]
        );
        let (first, second) = (&manifest.producers[0], &manifest.producers[1]);
        assert_eq!(first.flocq_objects.len(), second.flocq_objects.len());
        for (left, right) in first.flocq_objects.iter().zip(&second.flocq_objects) {
            assert_eq!(left.path, right.path);
            assert_ne!(left.sha256, right.sha256, "{}", left.path);
        }
        Ok(())
    }

    #[test]
    fn a_manifest_with_a_shared_plugin_digest_or_old_schema_is_rejected() -> Result<()> {
        let shared = PINNED_FLOCQ_MANIFEST.replace(
            "5a8480da6ef6fbb19e3d4a62ab3c0e6f",
            "1014006bc3627f54b6f91150cf1d341b",
        );
        assert!(parse_flocq_manifest(&shared).is_err());
        let old = PINNED_FLOCQ_MANIFEST.replace("\"schema_version\": 2", "\"schema_version\": 1");
        assert!(parse_flocq_manifest(&old).is_err());
        let unsorted = PINNED_FLOCQ_MANIFEST
            .replace(PRODUCER_A, "zz-first")
            .replace(PRODUCER_B, PRODUCER_A)
            .replace("zz-first", PRODUCER_B);
        assert!(parse_flocq_manifest(&unsorted).is_err());
        Ok(())
    }

    #[test]
    fn the_flocq_fixture_evidence_equals_its_producer_entry() -> Result<()> {
        let evidence: serde_json::Value = serde_json::from_str(FLOCQ_EVIDENCE)?;
        assert_eq!(evidence["flocq_producer"], PRODUCER_A);
        check_flocq_producer(
            &pinned_flocq_manifest()?,
            evidence["flocq_producer"].as_str(),
            &fixture_objects(),
        )
    }

    #[test]
    fn each_recorded_producer_admits_its_own_objects() -> Result<()> {
        let manifest = pinned_flocq_manifest()?;
        for producer in &manifest.producers {
            check_flocq_producer(
                &manifest,
                Some(producer.name.as_str()),
                &producer.flocq_objects,
            )?;
        }
        Ok(())
    }

    #[test]
    fn an_unrecorded_producer_is_rejected() -> Result<()> {
        let text = rejection(Some("fedora-44-gcc-16.1.0"), &producer_objects(PRODUCER_A)?)?;
        assert!(text.contains("fedora-44-gcc-16.1.0"), "{text}");
        assert!(text.contains("not in the pinned manifest"), "{text}");
        Ok(())
    }

    #[test]
    fn a_missing_producer_name_is_rejected() -> Result<()> {
        let text = rejection(None, &producer_objects(PRODUCER_A)?)?;
        assert!(text.contains("lack their flocq_producer"), "{text}");
        Ok(())
    }

    #[test]
    fn one_producers_digests_under_another_producers_name_are_rejected() -> Result<()> {
        for (digests, name) in [(PRODUCER_A, PRODUCER_B), (PRODUCER_B, PRODUCER_A)] {
            let text = rejection(Some(name), &producer_objects(digests)?)?;
            assert!(text.contains(name), "{text}");
            assert!(text.contains("external/Flocq/Calc/Bracket.vo"), "{text}");
            assert!(text.contains("differs from the pinned manifest"), "{text}");
        }
        Ok(())
    }

    #[test]
    fn a_changed_digest_is_rejected_at_its_path() -> Result<()> {
        let manifest = producer_objects(PRODUCER_A)?;
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
        let manifest = producer_objects(PRODUCER_A)?;
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
        let manifest = producer_objects(PRODUCER_A)?;
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
