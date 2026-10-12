use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const TARGETS: [&str; 1] = ["verified/C1463_ArithmeticInventory.v"];
const ARTIFACT_ROOT: &str = "data/output/audit/boolean-permutation-evidence/arithmetic-kernel";

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
    let mut result = BTreeSet::new();
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
            result.insert(
                modules
                    .get(&logical)
                    .unwrap_or_else(|| panic!("unlisted import {logical}"))
                    .clone(),
            );
        }
    }
    result.into_iter().collect()
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

fn declarations(source: &str) -> Vec<(String, String)> {
    source_commands(source)
        .into_iter()
        .filter_map(|command| {
            let words: Vec<_> = command.split_whitespace().collect();
            let position = usize::from(matches!(
                words.first(),
                Some(&"Local" | &"Global" | &"Polymorphic" | &"Monomorphic")
            ));
            if matches!(
                words.get(position),
                Some(&"Theorem" | &"Lemma" | &"Corollary" | &"Fact" | &"Proposition" | &"Example")
            ) {
                Some((
                    words[position + 1].trim_end_matches(':').to_owned(),
                    words.join(" "),
                ))
            } else {
                None
            }
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
    let mut command = Command::new("rocq");
    command.env(
        "PATH",
        format!("{}:{}", pin.display(), std::env::var("PATH").unwrap()),
    );
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
    for block in contents.split("Declaration: ").skip(1) {
        let (name, report) = block.split_once('\n').unwrap();
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

fn main() {
    let arguments: Vec<_> = std::env::args().collect();
    assert_eq!(
        arguments.len(),
        4,
        "usage: retained_rocq_execution REPOSITORY SCRATCH PINNED_BIN"
    );
    let root = Path::new(&arguments[1]);
    let scratch = Path::new(&arguments[2]);
    let pin = Path::new(&arguments[3]);
    let project_path = root.join("proofs/_RocqProject");
    let project_bytes = fs::read(&project_path).unwrap();
    let project_hash = sha256(&project_path);
    let project = String::from_utf8(project_bytes.clone()).unwrap();
    assert!(project.contains("-arg +default"));
    let modules: BTreeMap<_, _> = project
        .lines()
        .map(str::trim)
        .filter(|line| line.ends_with(".v") && !line.starts_with('#'))
        .map(|source| (logical_module(source), source.to_owned()))
        .collect();
    let work = scratch.join("proofs");
    let output = scratch.join("arithmetic-kernel");
    fs::create_dir_all(work.join("theories")).unwrap();
    fs::create_dir_all(work.join("verified")).unwrap();
    fs::create_dir_all(output.join("theories")).unwrap();
    fs::create_dir_all(output.join("verified")).unwrap();
    fs::write(output.join("_RocqProject.snapshot"), &project_bytes).unwrap();
    let toolchain = rocq(pin).arg("--version").output().unwrap();
    assert!(toolchain.status.success());
    assert_eq!(
        String::from_utf8(toolchain.stdout.clone()).unwrap().trim(),
        "The Rocq Prover, version 9.1.1\ncompiled with OCaml 5.4.0"
    );
    fs::write(output.join("toolchain.txt"), toolchain.stdout).unwrap();
    let mut union = BTreeSet::new();
    let mut compilation_order = Vec::new();
    let mut closures = BTreeMap::new();
    for target in TARGETS {
        let mut closure = BTreeSet::new();
        visit(root, target, &modules, &mut closure, &mut Vec::new());
        closures.insert(target.to_owned(), closure);
        visit(root, target, &modules, &mut union, &mut compilation_order);
    }
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
        let arguments = compiler_arguments(source, "+all");
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
    for target in TARGETS {
        let stem = Path::new(target).file_stem().unwrap().to_str().unwrap();
        let names = declarations(&fs::read_to_string(work.join(target)).unwrap());
        let logical = logical_module(target);
        let mut query = format!("Require Import {logical}.\n");
        for (name, _) in &names {
            query.push_str(&format!("Goal True.\n  idtac \"Declaration: {name}\".\n  exact I.\nQed.\nPrint Assumptions {logical}.{name}.\n"));
        }
        let query_source = format!("{stem}AssumptionQuery.v");
        fs::write(work.join(&query_source), &query).unwrap();
        fs::write(output.join(format!("{stem}.assumption-query.v")), query).unwrap();
        let status = execute(
            pin,
            &work,
            &compiler_arguments(&query_source, "+all"),
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
    let mut declaration_total = 0;
    let mut closed_total = 0;
    let mut assumption_total = 0;
    for target in TARGETS {
        let stem = Path::new(target).file_stem().unwrap().to_str().unwrap();
        let names = declarations(&fs::read_to_string(work.join(target)).unwrap());
        let log = fs::read_to_string(output.join(format!("{stem}.assumptions.txt"))).unwrap();
        let reports = log_assumptions(&log);
        assert_eq!(reports.len(), names.len());
        assert!(
            fs::read_to_string(output.join(format!("{stem}.kernel.txt")))
                .unwrap()
                .contains("CONTEXT SUMMARY")
        );
        let compile_command = format!("rocq {}", compiler_arguments(target, "+all").join(" "));
        let kernel_command = format!("rocq {}", checker_arguments(target).join(" "));
        let mut draft = format!(
            "schema_version = 1\nstable_id = {}\nproof_path = {}\nproject_sha256 = {}\ncompile_command = {}\nkernel_command = {}\ntoolchain = \"Rocq 9.1.1; OCaml 5.4.0\"\ncompile_exit_code = 0\nkernel_exit_code = 0\nwarning_policy = \"fatal_all\"\n",
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
    let summary = format!(
        "targets={}\nfirst_party_sources={}\nretained_proof_objects={}\nwitnessed_declarations={}\nclosed_declaration_queries={}\nprinted_assumption_name_occurrences={}\nproject_sha256={project_hash}\nwarning_policy=fatal_all\nraw_log_transformation=none\n",
        TARGETS.len(),
        union.len(),
        compilation_order.len(),
        declaration_total,
        closed_total,
        assumption_total
    );
    fs::write(output.join("execution-summary.txt"), &summary).unwrap();
    print!("{summary}");
    let mut artifacts: Vec<PathBuf> = Vec::new();
    for entry in fs::read_dir(&output).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            artifacts.push(entry.path());
        } else {
            for nested in fs::read_dir(entry.path()).unwrap() {
                artifacts.push(nested.unwrap().path());
            }
        }
    }
    artifacts.sort();
    let manifest = artifacts
        .into_iter()
        .map(|path| {
            format!(
                "{}  {}\n",
                sha256(&path),
                path.strip_prefix(&output).unwrap().display()
            )
        })
        .collect::<String>();
    fs::write(output.join("SHA256SUMS"), manifest).unwrap();
}
