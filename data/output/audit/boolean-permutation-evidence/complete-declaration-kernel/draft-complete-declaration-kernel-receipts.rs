use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

const NARRATIVE: &str = "The source owns the stated formal scope. Append-only source-bound execution receipts determine kernel_checked admission independently of explanatory metadata.";

fn digest_text(value: &str) -> String {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(value.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned()
}

fn collect_files(root: &Path, files: &mut Vec<std::path::PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let entry = entry.unwrap();
        let file_type = entry.file_type().unwrap();
        assert!(!file_type.is_symlink());
        if file_type.is_dir() {
            collect_files(&entry.path(), files);
        } else {
            assert!(file_type.is_file());
            files.push(entry.path());
        }
    }
}

fn main() {
    let arguments: Vec<_> = std::env::args().collect();
    assert!(
        (3..=4).contains(&arguments.len()),
        "usage: draft_complete_kernel_receipts KERNEL NEW_RECEIPT_DIRECTORY [C1463_EXPECTED_STATUS]"
    );
    let arithmetic_status = arguments
        .get(3)
        .map(String::as_str)
        .unwrap_or("source_only");
    assert!(matches!(
        arithmetic_status,
        "source_only" | "kernel_checked"
    ));
    let kernel = Path::new(&arguments[1]);
    let output = Path::new(&arguments[2]);
    fs::create_dir(output).unwrap();
    let narrative_digest = digest_text(NARRATIVE);
    let empty_digest = digest_text("");
    let mut files = Vec::new();
    collect_files(kernel, &mut files);
    assert!(files.len() >= 93);
    let mut objects = 0;
    let mut declarations = 0;
    let mut closed = 0;
    let mut assumptions = 0;
    let mut receipts = 0;
    let mut states = String::from("stable_id\texpected_status\texpected_kernel_result_sha256\n");
    let mut expected_files = BTreeSet::new();
    for line in fs::read_to_string(kernel.join("SHA256SUMS"))
        .unwrap()
        .lines()
    {
        let (hash, name) = line.split_once("  ").unwrap();
        assert_eq!(hash.len(), 64);
        assert!(expected_files.insert(name.to_owned()));
    }
    assert_eq!(expected_files.len() + 1, files.len());
    let mut source_names = std::collections::BTreeMap::<String, BTreeSet<String>>::new();
    let mut kind_counts = std::collections::BTreeMap::<String, usize>::new();
    for line in fs::read_to_string(kernel.join("recognized-declarations.tsv"))
        .unwrap()
        .lines()
        .skip(1)
    {
        let fields: Vec<_> = line.split('\t').collect();
        assert_eq!(fields.len(), 3);
        assert!(
            source_names
                .entry(fields[0].to_owned())
                .or_default()
                .insert(fields[2].to_owned())
        );
        *kind_counts.entry(fields[1].to_owned()).or_default() += 1;
    }
    assert_eq!(source_names.len(), 13);
    assert_eq!(kind_counts.get("Definition"), Some(&62));
    assert_eq!(kind_counts.get("Lemma"), Some(&63));
    assert_eq!(kind_counts.get("Theorem"), Some(&126));
    for file in &files {
        let relative = file.strip_prefix(kernel).unwrap().to_str().unwrap();
        assert!(relative == "SHA256SUMS" || expected_files.contains(relative));
        let bytes = fs::read(file).unwrap();
        for directory in ["home", "root", "tmp", "run/user", "var/tmp"] {
            let pattern = format!("/{directory}/");
            assert!(
                !bytes
                    .windows(pattern.len())
                    .any(|window| window == pattern.as_bytes()),
                "local path in {relative}"
            );
        }
        if file.extension().and_then(|value| value.to_str()) == Some("vo") {
            assert!(bytes.starts_with(b"Coq!"));
            objects += 1;
        }
        if relative.ends_with(".assumptions.txt") {
            let contents = String::from_utf8(bytes).unwrap();
            let count = contents.matches("Declaration:").count();
            let closed_count = contents
                .lines()
                .filter(|line| *line == "Closed under the global context")
                .count();
            let assumption_count = contents
                .lines()
                .filter(|line| *line == "Axioms:" || *line == "Section Variables:")
                .count();
            assert_eq!(count, closed_count + assumption_count);
            declarations += count;
            closed += closed_count;
            assumptions += assumption_count;
        }
        if relative.ends_with(".kernel.txt") {
            let contents = fs::read_to_string(file).unwrap();
            assert!(contents.contains("CONTEXT SUMMARY"));
        }
        let Some(stem) = relative.strip_suffix(".witness.toml") else {
            continue;
        };
        assert!(!stem.contains('/'));
        let witness = fs::read_to_string(file).unwrap();
        assert!(witness.is_ascii());
        let source = witness
            .lines()
            .find_map(|line| {
                line.strip_prefix("proof_path = \"")
                    .and_then(|value| value.strip_suffix('"'))
            })
            .unwrap();
        let mut witness_names = BTreeSet::new();
        for name in witness.lines().filter_map(|line| {
            line.strip_prefix("name = \"")
                .and_then(|value| value.strip_suffix('"'))
        }) {
            assert!(witness_names.insert(name.to_owned()));
        }
        assert_eq!(&witness_names, source_names.get(source).unwrap());
        let log = fs::read_to_string(kernel.join(format!("{stem}.assumptions.txt"))).unwrap();
        let mut log_names = BTreeSet::new();
        for block in log.split("Declaration:").skip(1) {
            let name = block.split_once('\n').unwrap().0.trim();
            assert!(!name.is_empty() && name.is_ascii() && name.split_whitespace().count() == 1);
            assert!(log_names.insert(name.to_owned()));
        }
        assert_eq!(witness_names, log_names);
        let expected_digest =
            if matches!(stem, "C958_ZDGraphTopology" | "C958b_ZDAdjacencyAnalytical") {
                &empty_digest
            } else {
                &narrative_digest
            };
        let expected_status = if stem == "C1463_ArithmeticInventory" {
            arithmetic_status
        } else {
            "source_only"
        };
        let mut receipt = format!(
            "evidence_key = \"complete-declaration-kernel-{stem}-5507a888eedd\"\nactor = \"codex\"\nreason = \"Admit complete recognized source, witness and labeled-assumption name sets through fresh fatal-default compilation, independent kernel checks, exact declaration assumptions and retained proof objects while preserving historical receipts.\"\napplied_at = \"2026-10-12T17:20:43Z\"\nexpected_kernel_result_sha256 = \"{expected_digest}\"\nexpected_status = \"{expected_status}\"\n\n[witness]\n"
        );
        for line in witness.lines() {
            if let Some(header) = line
                .strip_prefix("[[")
                .and_then(|value| value.strip_suffix("]]"))
            {
                receipt.push_str(&format!("[[witness.{header}]]\n"));
            } else if let Some(header) = line
                .strip_prefix('[')
                .and_then(|value| value.strip_suffix(']'))
            {
                receipt.push_str(&format!("[witness.{header}]\n"));
            } else {
                receipt.push_str(line);
                receipt.push('\n');
            }
        }
        let declaration_count = witness
            .lines()
            .filter(|line| *line == "[[declarations]]")
            .count();
        assert!(declaration_count > 0);
        fs::write(output.join(format!("{stem}.receipt.toml")), receipt).unwrap();
        states.push_str(&format!(
            "THM-LEGACY-{stem}\t{expected_status}\t{expected_digest}\n"
        ));
        receipts += 1;
    }
    assert_eq!(
        (objects, declarations, closed, assumptions, receipts),
        (16, 251, 224, 27, 13)
    );
    fs::write(output.join("receipt-prestates.tsv"), states).unwrap();
    let mut receipt_files: Vec<_> = fs::read_dir(output)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    receipt_files.sort();
    assert_eq!(receipt_files.len(), 14);
    let mut checksums = String::new();
    for path in receipt_files {
        let hash = Command::new("sha256sum").arg(&path).output().unwrap();
        assert!(hash.status.success());
        let hash = String::from_utf8(hash.stdout)
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned();
        checksums.push_str(&format!(
            "{hash}  {}\n",
            path.file_name().unwrap().to_str().unwrap()
        ));
    }
    fs::write(output.join("SHA256SUMS"), checksums).unwrap();
    println!(
        "audited_files={}\nmanifest_entries={}\nproof_object_headers=16\nlabeled_queries=251\nclosed_queries=224\nassumption_bearing_queries=27\nrecognized_Definition_declarations=62\nrecognized_Lemma_declarations=63\nrecognized_Theorem_declarations=126\nrecognized_source_witness_log_name_sets=equal\nlocal_path_matches=0\nreceipt_drafts=13\npostbinding_narrative_sha256={narrative_digest}\nunchanged_empty_narrative_sha256={empty_digest}",
        files.len(),
        expected_files.len()
    );
}
