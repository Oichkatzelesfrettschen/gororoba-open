use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

const TARGETS: [&str; 25] = [
    "theories/BooleanPermutation.v",
    "theories/FoldAverageDescent.v",
    "theories/TerminalChannelSeparation.v",
    "theories/TerminalChannelSeparationReal.v",
    "theories/SignCodeProjection.v",
    "theories/SchreierSignCode.v",
    "theories/SignCodeCardinality.v",
    "theories/BooleanCochainFiltration.v",
    "theories/SedenionMembershipConstraints.v",
    "theories/MinimalUncurvedObstruction.v",
    "verified/C958_ZDGraphTopology.v",
    "verified/C958b_ZDAdjacencyAnalytical.v",
    "verified/C1463_ArithmeticInventory.v",
    "verified/C881_GF2CubicMinDegree.v",
    "verified/C014_AnnihilatorDim4.v",
    "theories/NullityTwelveQuadraticLocus.v",
    "theories/SedenionFoldTransport.v",
    "theories/PassiveMechanicalMemory.v",
    "theories/FiniteComplexPassivity.v",
    "theories/VacuumCounterexamples.v",
    "theories/GaussianCoherence.v",
    "theories/WorldlineInteraction.v",
    "theories/VacuumSpectralModels.v",
    "theories/FiniteCompositePassivity.v",
    "theories/VacuumAnalyticLimits.v",
];
const ARTIFACT_ROOT: &str = "data/output/audit/vacuum-composition/kernel-capture";
const EXPECTED_PROJECT_SHA256: &str =
    "1c1c11f503da08cb3df276d8a657b100bff467290c6fb5191ef2aeb1cff6c839";
const HISTORICAL_ROOTS: [&str; 3] = [
    "data/output/audit/boolean-permutation-evidence/kernel",
    "data/output/audit/boolean-permutation-evidence/arithmetic-kernel",
    "data/output/audit/boolean-permutation-evidence/complete-declaration-kernel",
];

fn source_commands(source: &str) -> Vec<String> {
    let characters: Vec<_> = source.chars().collect();
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
                && next.is_none_or(|value| value.is_whitespace() || value == '(')
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
    assert_eq!(depth, 0, "unterminated source comment");
    assert!(!quoted, "unterminated source string");
    if !visible.trim().is_empty() {
        commands.push(visible.trim().to_owned());
    }
    commands
}

fn logical_module(source: &str) -> String {
    let (source_root, name) = source.split_once('/').unwrap();
    let namespace = if source_root == "theories" {
        "OpenGororoba"
    } else {
        "OpenGororobaVerified"
    };
    format!(
        "{namespace}.{}",
        name.trim_end_matches(".v").replace('/', ".")
    )
}

fn imports(root: &Path, source: &str, modules: &BTreeMap<String, String>) -> Vec<String> {
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    for command in source_commands(&fs::read_to_string(root.join("proofs").join(source)).unwrap()) {
        let words: Vec<_> = command.split_whitespace().collect();
        assert_ne!(words.first(), Some(&"Load"), "dynamic source Load");
        let (namespace, require_position) = if words.first() == Some(&"From")
            && words.get(2) == Some(&"Require")
        {
            let namespace = words[1];
            if !["OpenGororoba", "OpenGororobaVerified"]
                .iter()
                .any(|prefix| namespace == *prefix || namespace.starts_with(&format!("{prefix}.")))
            {
                continue;
            }
            (Some(namespace), 2)
        } else if words.first() == Some(&"Require") {
            (None, 0)
        } else {
            continue;
        };
        let first_module = require_position
            + if matches!(words.get(require_position + 1), Some(&"Import" | &"Export")) {
                2
            } else {
                1
            };
        for name in words.iter().skip(first_module) {
            let logical = if let Some(namespace) = namespace {
                format!("{namespace}.{name}")
            } else if name.starts_with("OpenGororoba.") || name.starts_with("OpenGororobaVerified.")
            {
                (*name).to_owned()
            } else {
                let matching: Vec<_> = modules
                    .keys()
                    .filter(|logical| logical.rsplit('.').next() == Some(*name))
                    .collect();
                assert!(matching.len() <= 1, "ambiguous first-party import");
                if let Some(logical) = matching.first() {
                    (*logical).clone()
                } else {
                    continue;
                }
            };
            let dependency = modules
                .get(&logical)
                .unwrap_or_else(|| panic!("unlisted import {logical}"))
                .clone();
            if seen.insert(dependency.clone()) {
                result.push(dependency);
            }
        }
    }
    result
}

fn visit(
    root: &Path,
    source: &str,
    modules: &BTreeMap<String, String>,
    visited: &mut BTreeSet<String>,
    ordered: &mut Vec<String>,
) {
    if !visited.insert(source.to_owned()) {
        return;
    }
    for dependency in imports(root, source, modules) {
        visit(root, &dependency, modules, visited, ordered);
    }
    ordered.push(source.to_owned());
}

fn has_top_level_mutual_declaration(command: &str) -> bool {
    let mut delimiter_depth = 0usize;
    let mut match_depth = 0usize;
    let mut quoted = false;
    let mut token = String::new();
    let inspect = |token: &str, delimiter_depth: usize, match_depth: &mut usize| {
        match token {
            "match" => *match_depth += 1,
            "end" => *match_depth = match_depth.saturating_sub(1),
            "with" if delimiter_depth == 0 && *match_depth == 0 => return true,
            _ => {}
        }
        false
    };
    for character in command.chars() {
        if !quoted && (character.is_alphanumeric() || matches!(character, '_' | '\'')) {
            token.push(character);
            continue;
        }
        if inspect(&token, delimiter_depth, &mut match_depth) {
            return true;
        }
        token.clear();
        if character == '"' {
            quoted = !quoted;
        } else if !quoted {
            match character {
                '(' | '[' | '{' => delimiter_depth += 1,
                ')' | ']' | '}' => delimiter_depth = delimiter_depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    inspect(&token, delimiter_depth, &mut match_depth)
}

fn declarations(source: &str) -> Vec<(String, String)> {
    let result: Vec<_> = source_commands(source)
        .into_iter()
        .filter_map(|command| {
            let words: Vec<_> = command.split_whitespace().collect();
            let position = usize::from(matches!(
                words.first(),
                Some(&"Local" | &"Global" | &"Polymorphic" | &"Monomorphic")
            ));
            let supported = |keyword: &str| {
                matches!(
                    keyword,
                    "Theorem"
                        | "Lemma"
                        | "Corollary"
                        | "Fact"
                        | "Proposition"
                        | "Definition"
                        | "Example"
                )
            };
            let context = |keyword: &str| {
                matches!(
                    keyword,
                    "Axiom"
                        | "Axioms"
                        | "Parameter"
                        | "Parameters"
                        | "Variable"
                        | "Variables"
                        | "Hypothesis"
                        | "Hypotheses"
                        | "Context"
                        | "Inductive"
                        | "CoInductive"
                        | "Variant"
                        | "Record"
                        | "Structure"
                        | "Class"
                        | "Fixpoint"
                        | "CoFixpoint"
                )
            };
            let header = words.get(position).copied().unwrap_or_default();
            let mut source_words = command
                .split('"')
                .step_by(2)
                .flat_map(str::split_whitespace);
            if !supported(header) && !context(header) {
                assert!(
                    !command
                        .split('"')
                        .step_by(2)
                        .any(|fragment| fragment.contains("#["))
                        && !source_words.any(|word| supported(word)
                            || context(word)
                            || matches!(
                                word,
                                "Remark"
                                    | "Let"
                                    | "Instance"
                                    | "Goal"
                                    | "Program"
                                    | "Equations"
                                    | "Function"
                                    | "Scheme"
                                    | "Obligation"
                                    | "Obligations"
                            )),
                    "unsupported proof declaration form or prefix"
                );
                return None;
            }
            if context(header) {
                return None;
            }
            assert!(
                !has_top_level_mutual_declaration(&command),
                "unsupported mutual proof declaration form"
            );
            if supported(header) {
                assert!(
                    words.len() > position + 1,
                    "recognized declaration lacks a name"
                );
                let name = words[position + 1].trim_end_matches(':');
                let mut characters = name.chars();
                assert!(
                    characters
                        .next()
                        .is_some_and(|character| character.is_alphabetic() || character == '_')
                        && characters.all(|character| character.is_alphanumeric()
                            || matches!(character, '_' | '\'')),
                    "unsupported proof declaration name syntax"
                );
                Some((name.to_owned(), words.join(" ")))
            } else {
                None
            }
        })
        .collect();
    let mut names = BTreeSet::new();
    for (name, _) in &result {
        assert!(
            names.insert(name.clone()),
            "duplicate recognized source declaration: {name}"
        );
    }
    result
}

fn declaration_kind(statement: &str) -> &str {
    let words: Vec<_> = statement.split_whitespace().collect();
    words[usize::from(matches!(
        words.first(),
        Some(&"Local" | &"Global" | &"Polymorphic" | &"Monomorphic")
    ))]
}

fn regular_files(root: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let entry = entry.unwrap();
        let file_type = entry.file_type().unwrap();
        assert!(!file_type.is_symlink(), "artifact path is a symlink");
        if file_type.is_dir() {
            regular_files(&entry.path(), files);
        } else {
            assert!(file_type.is_file(), "artifact path is not a regular file");
            files.push(entry.path());
        }
    }
}

fn historical_snapshot(root: &Path) -> BTreeMap<String, String> {
    let mut files = Vec::new();
    for historical_root in HISTORICAL_ROOTS {
        regular_files(&root.join(historical_root), &mut files);
    }
    files
        .into_iter()
        .map(|path| {
            (
                path.strip_prefix(root)
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_owned(),
                sha256(&path),
            )
        })
        .collect()
}

fn sha256(path: &Path) -> String {
    let output = Command::new("sha256sum").arg(path).output().unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned()
}

fn quote(value: &str) -> String {
    format!(
        "\"{}\"",
        value
            .replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\n', "\\n")
            .replace('\r', "\\r")
            .replace('\t', "\\t")
    )
}

fn rocq(pin: &Path) -> Command {
    let mut command = Command::new(pin.join("rocq"));
    command.env(
        "PATH",
        format!("{}:{}", pin.display(), std::env::var("PATH").unwrap()),
    );
    command.env_remove("COQPATH").env_remove("ROCQPATH");
    command
}

fn execute(pin: &Path, working: &Path, arguments: &[String], log: &Path) -> i32 {
    let output = File::create(log).unwrap();
    rocq(pin)
        .current_dir(working)
        .args(arguments)
        .stdout(Stdio::from(output.try_clone().unwrap()))
        .stderr(Stdio::from(output))
        .status()
        .unwrap()
        .code()
        .unwrap_or(-1)
}

fn compiler_arguments(source: &str, warning_policy: &str) -> Vec<String> {
    [
        "compile",
        "-q",
        "-w",
        warning_policy,
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
    .collect()
}

fn checker_arguments(source: &str) -> Vec<String> {
    [
        "check",
        "-silent",
        "-o",
        "-R",
        "theories",
        "OpenGororoba",
        "-R",
        "verified",
        "OpenGororobaVerified",
        &logical_module(source),
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

fn log_assumptions(contents: &str) -> BTreeMap<String, Vec<String>> {
    let mut result = BTreeMap::new();
    for block in contents.split("Declaration:").skip(1) {
        let (name, report) = block.split_once('\n').unwrap();
        assert!(
            !name.trim().is_empty() && name.is_ascii() && name.split_whitespace().count() == 1,
            "invalid assumption-log declaration label"
        );
        let mut assumptions = BTreeSet::new();
        let mut closed = false;
        let mut assumption_section = false;
        for line in report.lines() {
            let trimmed = line.trim();
            if trimmed == "Closed under the global context" {
                assert!(!assumption_section);
                closed = true;
            } else if trimmed == "Axioms:" || trimmed == "Section Variables:" {
                assert!(!closed);
                assumption_section = true;
            } else if assumption_section
                && !line.starts_with(char::is_whitespace)
                && let Some((name, _)) = line.split_once(':')
            {
                assert_eq!(name.trim().split_whitespace().count(), 1);
                assert!(assumptions.insert(name.trim().to_owned()));
            }
        }
        assert!(closed || (assumption_section && !assumptions.is_empty()));
        assert!(
            result
                .insert(name.trim().to_owned(), assumptions.into_iter().collect())
                .is_none()
        );
    }
    result
}

fn digest_table(name: &str, relative: &str, physical: &Path) -> String {
    format!(
        "\n[{name}]\npath = {}\nsha256 = {}\n",
        quote(relative),
        quote(&sha256(physical))
    )
}

fn write_manifest(output: &Path) {
    let mut artifacts = Vec::new();
    regular_files(output, &mut artifacts);
    artifacts.retain(|path| path.strip_prefix(output).unwrap() != Path::new("SHA256SUMS"));
    artifacts.sort();
    let manifest = artifacts
        .into_iter()
        .map(|path| {
            format!(
                "{}  {}\n",
                sha256(&path),
                path.strip_prefix(output).unwrap().display()
            )
        })
        .collect::<String>();
    fs::write(output.join("SHA256SUMS"), manifest).unwrap();
}

fn organize_witnesses(output: &Path) {
    let witnesses = output.join("witnesses");
    fs::create_dir(&witnesses).expect("witness directory already exists or cannot be created");
    for target in TARGETS {
        let stem = Path::new(target).file_stem().unwrap().to_str().unwrap();
        let filename = format!("{stem}.witness.toml");
        let source = output.join(&filename);
        assert!(fs::symlink_metadata(&source).unwrap().file_type().is_file());
        fs::rename(source, witnesses.join(filename)).unwrap();
    }
    write_manifest(output);
    println!("organized_raw_witnesses={}", TARGETS.len());
}

fn main() {
    let arguments: Vec<_> = std::env::args().collect();
    if arguments.len() == 3 && arguments[1] == "organize" {
        organize_witnesses(Path::new(&arguments[2]));
        return;
    }
    assert_eq!(
        arguments.len(),
        4,
        "usage: capture_rocq_receipts REPOSITORY SCRATCH PINNED_BIN"
    );
    let root = Path::new(&arguments[1]);
    let scratch = Path::new(&arguments[2]);
    let pin = Path::new(&arguments[3]);
    let historical_before = historical_snapshot(root);
    let project_path = root.join("proofs/_RocqProject");
    let project_bytes = fs::read(&project_path).unwrap();
    let project_hash = sha256(&project_path);
    assert_eq!(
        project_hash, EXPECTED_PROJECT_SHA256,
        "proof project changed before capture"
    );
    let project = String::from_utf8(project_bytes.clone()).unwrap();
    assert!(project.contains("-arg +default"));
    let modules: BTreeMap<_, _> = project
        .lines()
        .map(str::trim)
        .filter(|line| line.ends_with(".v") && !line.starts_with('#'))
        .map(|source| (logical_module(source), source.to_owned()))
        .collect();
    let work = scratch.join("proofs");
    let output = scratch.join("kernel");
    fs::create_dir(&output).expect("scratch kernel output already exists or cannot be created");
    fs::create_dir_all(work.join("theories")).unwrap();
    fs::create_dir_all(work.join("verified")).unwrap();
    fs::create_dir_all(output.join("theories")).unwrap();
    fs::create_dir_all(output.join("verified")).unwrap();
    fs::copy(
        root.join("data/output/audit/vacuum-composition/capture_rocq_receipts.rs"),
        output.join("capture_rocq_receipts.rs"),
    )
    .unwrap();
    fs::write(
        output.join("historical-artifacts.sha256"),
        historical_before
            .iter()
            .map(|(path, hash)| format!("{hash}  {path}\n"))
            .collect::<String>(),
    )
    .unwrap();
    fs::write(output.join("_RocqProject.snapshot"), &project_bytes).unwrap();
    let toolchain = rocq(pin).arg("--version").output().unwrap();
    assert!(toolchain.status.success());
    assert_eq!(
        String::from_utf8(toolchain.stdout.clone()).unwrap().trim(),
        "The Rocq Prover, version 9.3.0\ncompiled with OCaml 5.5.1"
    );
    fs::write(output.join("toolchain.txt"), toolchain.stdout).unwrap();
    let mut union = BTreeSet::new();
    let mut compilation_order = Vec::new();
    let mut closures = BTreeMap::new();
    let mut target_orders = String::from("proof_path\tcompilation_position\tsource_path\n");
    for target in TARGETS {
        let mut closure = BTreeSet::new();
        let mut target_order = Vec::new();
        visit(root, target, &modules, &mut closure, &mut target_order);
        for (position, source) in target_order.iter().enumerate() {
            target_orders.push_str(&format!("proofs/{target}\t{position}\tproofs/{source}\n"));
        }
        closures.insert(target.to_owned(), closure);
        visit(root, target, &modules, &mut union, &mut compilation_order);
    }
    fs::write(output.join("target-compilation-orders.tsv"), target_orders).unwrap();
    let mut source_manifest = String::new();
    let mut source_hashes = BTreeMap::new();
    for source in &union {
        let original = root.join("proofs").join(source);
        assert!(
            fs::symlink_metadata(&original)
                .unwrap()
                .file_type()
                .is_file()
        );
        fs::copy(&original, work.join(source)).unwrap();
        let hash = sha256(&original);
        assert_eq!(hash, sha256(&work.join(source)));
        source_manifest.push_str(&format!("{hash}  proofs/{source}\n"));
        source_hashes.insert(source.to_owned(), hash);
    }
    fs::write(output.join("sources.sha256"), source_manifest).unwrap();
    let mut closure_manifest = String::new();
    for (target, closure) in &closures {
        for source in closure {
            closure_manifest.push_str(&format!(
                "proofs/{target}\tproofs/{source}\t{}\n",
                source_hashes[source]
            ));
        }
    }
    fs::write(output.join("source-closures.tsv"), closure_manifest).unwrap();
    let mut failed = false;
    for source in &compilation_order {
        let stem = Path::new(source).file_stem().unwrap().to_str().unwrap();
        let arguments = compiler_arguments(source, "+default");
        let status = execute(
            pin,
            &work,
            &arguments,
            &output.join(format!("{stem}.compile.txt")),
        );
        println!("compile {stem} exit {status}");
        if status != 0 {
            failed = true;
        }
    }
    assert!(
        !failed,
        "first-party compilation failed; inspect retained logs"
    );
    for source in &compilation_order {
        let object = work.join(source).with_extension("vo");
        assert!(fs::read(&object).unwrap().starts_with(b"Coq!"));
        fs::copy(&object, output.join(Path::new(source).with_extension("vo"))).unwrap();
    }
    let mut query_counts = BTreeMap::new();
    let mut recognized_manifest = String::from("proof_path\tdeclaration_kind\tdeclaration_name\n");
    let mut recognized_kind_counts = BTreeMap::<String, usize>::new();
    for target in TARGETS {
        let stem = Path::new(target).file_stem().unwrap().to_str().unwrap();
        let names = declarations(&fs::read_to_string(work.join(target)).unwrap());
        for (name, statement) in &names {
            let kind = declaration_kind(statement);
            *recognized_kind_counts.entry(kind.to_owned()).or_default() += 1;
            recognized_manifest.push_str(&format!("proofs/{target}\t{kind}\t{name}\n"));
        }
        let logical = logical_module(target);
        let mut query = format!("Require Import {logical}.\n");
        for (name, _) in &names {
            query.push_str(&format!("Goal True.\nProof.\n  idtac \"Declaration: {name}\".\n  exact I.\nQed.\nPrint Assumptions {logical}.{name}.\n"));
        }
        let query_source = format!("{stem}AssumptionQuery.v");
        fs::write(work.join(&query_source), &query).unwrap();
        fs::write(output.join(format!("{stem}.assumption-query.v")), query).unwrap();
        let status = execute(
            pin,
            &work,
            &compiler_arguments(&query_source, "+default"),
            &output.join(format!("{stem}.assumptions.txt")),
        );
        println!(
            "assumptions {stem} exit {status} declarations {}",
            names.len()
        );
        assert_eq!(status, 0);
        query_counts.insert(stem.to_owned(), names.len());
    }
    std::thread::scope(|scope| {
        let handles: Vec<_> = TARGETS
            .into_iter()
            .map(|target| {
                let work = &work;
                let output = &output;
                scope.spawn(move || {
                    let stem = Path::new(target).file_stem().unwrap().to_str().unwrap();
                    let status = execute(
                        pin,
                        work,
                        &checker_arguments(target),
                        &output.join(format!("{stem}.kernel.txt")),
                    );
                    println!("kernel {stem} exit {status}");
                    assert_eq!(status, 0);
                })
            })
            .collect();
        for handle in handles {
            handle.join().unwrap();
        }
    });
    fs::write(
        output.join("recognized-declarations.tsv"),
        recognized_manifest,
    )
    .unwrap();
    let mut declaration_total = 0;
    let mut closed_total = 0;
    let mut assumption_total = 0;
    for target in TARGETS {
        let stem = Path::new(target).file_stem().unwrap().to_str().unwrap();
        let names = declarations(&fs::read_to_string(work.join(target)).unwrap());
        let log = fs::read_to_string(output.join(format!("{stem}.assumptions.txt"))).unwrap();
        let reports = log_assumptions(&log);
        assert_eq!(reports.len(), names.len());
        let source_names: BTreeSet<_> = names.iter().map(|(name, _)| name.clone()).collect();
        let logged_names: BTreeSet<_> = reports.keys().cloned().collect();
        assert_eq!(
            source_names, logged_names,
            "source/log declaration set differs for {stem}"
        );
        assert!(
            fs::read_to_string(output.join(format!("{stem}.kernel.txt")))
                .unwrap()
                .contains("CONTEXT SUMMARY")
        );
        let compile_command = format!("rocq {}", compiler_arguments(target, "+default").join(" "));
        let kernel_command = format!("rocq {}", checker_arguments(target).join(" "));
        let mut draft = format!(
            "schema_version = 1\nstable_id = {}\nproof_path = {}\nproject_sha256 = {}\ncompile_command = {}\nkernel_command = {}\ntoolchain = \"Rocq 9.3.0; OCaml 5.5.1\"\ncompile_exit_code = 0\nkernel_exit_code = 0\nwarning_policy = \"fatal_default\"\n",
            quote(&format!("THM-LEGACY-{stem}")),
            quote(&format!("proofs/{target}")),
            quote(&project_hash),
            quote(&compile_command),
            quote(&kernel_command)
        );
        for source in &closures[target] {
            draft.push_str(&format!(
                "\n[[sources]]\npath = {}\nsha256 = {}\n",
                quote(&format!("proofs/{source}")),
                quote(&source_hashes[source])
            ));
        }
        for (role, suffix) in [
            ("compile_log", "compile.txt"),
            ("kernel_log", "kernel.txt"),
            ("assumption_log", "assumptions.txt"),
        ] {
            let name = format!("{stem}.{suffix}");
            draft.push_str(&digest_table(
                role,
                &format!("{ARTIFACT_ROOT}/{name}"),
                &output.join(name),
            ));
        }
        let object = Path::new(target).with_extension("vo");
        draft.push_str(&digest_table(
            "proof_object",
            &format!("{ARTIFACT_ROOT}/{}", object.display()),
            &output.join(object),
        ));
        for (name, statement) in names {
            let assumptions = &reports[&name];
            declaration_total += 1;
            if assumptions.is_empty() {
                closed_total += 1;
            }
            assumption_total += assumptions.len();
            draft.push_str(&format!(
                "\n[[declarations]]\nname = {}\nstatement = {}\nassumptions = [{}]\n",
                quote(&name),
                quote(&statement),
                assumptions
                    .iter()
                    .map(|value| quote(value))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        fs::write(output.join(format!("{stem}.witness.toml")), draft).unwrap();
        let serialized = fs::read_to_string(output.join(format!("{stem}.witness.toml"))).unwrap();
        let mut witness_names = BTreeSet::new();
        let mut declaration_header = false;
        for line in serialized.lines() {
            if line == "[[declarations]]" {
                declaration_header = true;
            } else if declaration_header {
                let name = line
                    .strip_prefix("name = \"")
                    .and_then(|value| value.strip_suffix('"'))
                    .expect("declaration section lacks its serialized name");
                assert!(
                    witness_names.insert(name.to_owned()),
                    "duplicate serialized witness declaration"
                );
                declaration_header = false;
            }
        }
        assert_eq!(
            source_names, witness_names,
            "source/witness declaration set differs for {stem}"
        );
    }
    assert_eq!(
        project_hash,
        sha256(&project_path),
        "project changed during execution"
    );
    for (source, expected) in &source_hashes {
        assert_eq!(
            expected,
            &sha256(&root.join("proofs").join(source)),
            "source changed during execution: {source}"
        );
    }
    assert_eq!(
        historical_before,
        historical_snapshot(root),
        "historical artifact path sets or bytes changed during execution"
    );
    let summary = format!(
        "targets={}\nfirst_party_sources={}\nretained_proof_objects={}\nwitnessed_declarations={}\nclosed_declaration_queries={}\nprinted_assumption_name_occurrences={}\nproject_sha256={project_hash}\nwarning_policy=fatal_default\nraw_log_transformation=none\nrecognized_source_witness_log_name_sets=equal\nhistorical_artifact_name_sets_and_bytes=identical\nhistorical_artifact_files={}\n",
        TARGETS.len(),
        union.len(),
        compilation_order.len(),
        declaration_total,
        closed_total,
        assumption_total,
        historical_before.len()
    );
    let kind_summary = recognized_kind_counts
        .iter()
        .map(|(kind, count)| format!("recognized_{kind}_declarations={count}\n"))
        .collect::<String>();
    fs::write(
        output.join("execution-summary.txt"),
        format!("{summary}{kind_summary}"),
    )
    .unwrap();
    for entry in fs::read_dir(&output).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|extension| extension == "txt") {
            let contents = fs::read_to_string(&path).unwrap();
            for prefix in ["/home/", "/root/", "/tmp/", "/run/user/", "/var/tmp/"] {
                assert!(
                    !contents.contains(prefix),
                    "retained output contains a local path"
                );
            }
            assert!(
                !contents
                    .lines()
                    .any(|line| line.trim_start().starts_with("Warning:")),
                "retained output contains a warning"
            );
        }
    }
    print!("{summary}{kind_summary}");
    write_manifest(&output);
}

#[cfg(test)]
mod tests {
    use super::{declarations, log_assumptions};

    #[test]
    fn seven_recognized_kinds_and_single_modifiers_are_complete() {
        let kinds = [
            "Theorem",
            "Lemma",
            "Corollary",
            "Fact",
            "Proposition",
            "Definition",
            "Example",
        ];
        for modifier in ["", "Local ", "Global ", "Polymorphic ", "Monomorphic "] {
            let source = kinds
                .iter()
                .enumerate()
                .map(|(index, kind)| format!("{modifier}{kind} declaration_{index} : True := I.\n"))
                .collect::<String>();
            let result = declarations(&source);
            assert_eq!(result.len(), kinds.len());
            for (index, (name, statement)) in result.iter().enumerate() {
                assert_eq!(name, &format!("declaration_{index}"));
                assert_eq!(
                    statement,
                    &format!("{modifier}{} declaration_{index} : True := I", kinds[index])
                );
            }
        }
    }

    #[test]
    fn unsupported_attributes_and_wrappers_fail_visibly() {
        for source in [
            "#[global] Definition hidden := True.",
            "Local#[local]Theorem hidden : True.",
            "Program Definition hidden := True.",
            "Fail Definition hidden := True.",
            "Global Polymorphic Definition hidden := True.",
            "Remark hidden : True.",
            "Let hidden := True.",
            "Instance hidden : True.",
            "Goal True.",
        ] {
            assert!(std::panic::catch_unwind(|| declarations(source)).is_err());
        }
    }

    #[test]
    fn duplicate_source_and_labeled_log_names_are_rejected() {
        assert!(
            std::panic::catch_unwind(|| declarations(
                "Definition repeated := True. Definition repeated := False."
            ))
            .is_err()
        );
        assert!(std::panic::catch_unwind(|| log_assumptions("Declaration: repeated\nClosed under the global context\nDeclaration: repeated\nClosed under the global context\n")).is_err());
    }

    #[test]
    fn compile_context_forms_remain_outside_the_named_denominator() {
        let source = "Axiom premise : True. Parameter parameter : Type. Inductive carrier := element. Record record_carrier := { field : True }. Fixpoint recursion (value : nat) := value. CoFixpoint corecursion := corecursion.";
        assert!(declarations(source).is_empty());
    }

    #[test]
    fn mutual_headers_reject_while_definition_match_bodies_remain_complete() {
        assert!(
            std::panic::catch_unwind(|| declarations("Theorem first : True with second : True."))
                .is_err()
        );
        let source =
            "Definition pick (value : bool) := match value with true => true | false => false end.";
        let result = declarations(source);
        assert_eq!(
            result,
            vec![("pick".to_owned(), source.trim_end_matches('.').to_owned())]
        );
    }

    #[test]
    fn declaration_markers_without_spacing_are_visible_and_duplicate_checked() {
        let reports = log_assumptions(
            "Declaration: declared\nClosed under the global context\nDeclaration:extra\nClosed under the global context\n",
        );
        assert_eq!(
            reports.keys().map(String::as_str).collect::<Vec<_>>(),
            vec!["declared", "extra"]
        );
        assert!(std::panic::catch_unwind(|| log_assumptions("Declaration: repeated\nClosed under the global context\nDeclaration:repeated\nClosed under the global context\n")).is_err());
    }

    #[test]
    fn quoted_attribute_literals_preserve_the_ordinary_command_boundary() {
        assert!(declarations("Check \"#[local]Theorem\".").is_empty());
        let source = "Definition quoted := \"#[local]Theorem\".";
        assert_eq!(
            declarations(source),
            vec![("quoted".to_owned(), source.trim_end_matches('.').to_owned())]
        );
    }
}
