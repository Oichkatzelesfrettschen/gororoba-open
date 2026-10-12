use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn files(root: &Path, result: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let entry = entry.unwrap();
        let kind = entry.file_type().unwrap();
        assert!(!kind.is_symlink());
        if kind.is_dir() {
            files(&entry.path(), result);
        } else {
            assert!(kind.is_file());
            result.push(entry.path());
        }
    }
}

fn checksum(path: &Path) -> String {
    let output = Command::new("sha256sum").arg(path).output().unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned()
}

fn manifest(root: &Path, entries: &[PathBuf]) -> String {
    entries
        .iter()
        .map(|path| {
            format!(
                "{}  {}\n",
                checksum(path),
                path.strip_prefix(root).unwrap().display()
            )
        })
        .collect()
}

fn main() {
    let arguments: Vec<_> = std::env::args().collect();
    assert_eq!(
        arguments.len(),
        3,
        "usage: artifact_checksums refresh|verify ARTIFACT_ROOT"
    );
    let mode = arguments[1].as_str();
    assert!(matches!(mode, "refresh" | "verify"));
    let root = Path::new(&arguments[2]);
    let receipt_root = root.join("receipts");
    let mut receipts: Vec<_> = fs::read_dir(&receipt_root)
        .unwrap()
        .map(|entry| {
            let entry = entry.unwrap();
            assert!(entry.file_type().unwrap().is_file());
            entry.path()
        })
        .filter(|path| path.file_name().unwrap() != "SHA256SUMS")
        .collect();
    receipts.sort();
    assert_eq!(receipts.len(), 14);
    assert_eq!(
        receipts
            .iter()
            .filter(|path| path
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .ends_with(".receipt.toml"))
            .count(),
        13
    );
    let receipt_manifest = manifest(&receipt_root, &receipts);
    if mode == "refresh" {
        fs::write(receipt_root.join("SHA256SUMS"), &receipt_manifest).unwrap();
    } else {
        assert_eq!(
            fs::read_to_string(receipt_root.join("SHA256SUMS")).unwrap(),
            receipt_manifest
        );
    }
    let mut all = Vec::new();
    files(root, &mut all);
    all.retain(|path| path.strip_prefix(root).unwrap() != Path::new("SHA256SUMS"));
    all.sort();
    let mut names = BTreeSet::new();
    for path in &all {
        assert!(names.insert(path.strip_prefix(root).unwrap().to_owned()));
        let bytes = fs::read(path).unwrap();
        for directory in ["home", "root", "tmp", "run/user", "var/tmp"] {
            let pattern = format!("/{directory}/");
            assert!(
                !bytes
                    .windows(pattern.len())
                    .any(|value| value == pattern.as_bytes()),
                "local path in {}",
                path.strip_prefix(root).unwrap().display()
            );
        }
    }
    let complete_manifest = manifest(root, &all);
    if mode == "refresh" {
        fs::write(root.join("SHA256SUMS"), &complete_manifest).unwrap();
    } else {
        assert_eq!(
            fs::read_to_string(root.join("SHA256SUMS")).unwrap(),
            complete_manifest
        );
    }
    println!(
        "manifest_entries={}\nreceipt_manifest_entries=14\nlocal_path_matches=0\nmode={mode}",
        all.len()
    );
}
