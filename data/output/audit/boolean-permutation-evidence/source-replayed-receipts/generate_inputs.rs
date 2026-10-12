use std::{collections::BTreeSet, fs, path::Path, process::Command};

fn replace_header(input: &str, field: &str, value: &str) -> String {
    let prefix = format!("{field} = ");
    let mut matches = 0;
    let result = input
        .split_inclusive('\n')
        .map(|line| {
            if line.starts_with(&prefix) {
                matches += 1;
                format!("{field} = \"{value}\"\n")
            } else {
                line.to_owned()
            }
        })
        .collect();
    assert_eq!(matches, 1, "exactly one {field} header required");
    result
}

fn main() {
    let arguments: Vec<_> = std::env::args().collect();
    assert_eq!(
        arguments.len(),
        4,
        "INPUT_RECEIPTS NEW_OUTPUT UTC_TIMESTAMP"
    );
    let input_root = Path::new(&arguments[1]);
    let output_root = Path::new(&arguments[2]);
    let timestamp = &arguments[3];
    assert!(timestamp.len() == 20 && timestamp.ends_with('Z'));
    assert!(
        timestamp
            .chars()
            .all(|value| value.is_ascii_digit() || "-:TZ".contains(value))
    );
    let mut inputs: Vec<_> = fs::read_dir(input_root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .ends_with(".receipt.toml")
        })
        .collect();
    inputs.sort();
    assert_eq!(inputs.len(), 13);
    fs::create_dir(output_root).unwrap();
    let mut names = BTreeSet::new();
    let mut checksums = String::new();
    for input in inputs {
        assert!(
            input.is_file()
                && !fs::symlink_metadata(&input)
                    .unwrap()
                    .file_type()
                    .is_symlink()
        );
        let filename = input.file_name().unwrap().to_str().unwrap();
        let stem = filename.strip_suffix(".receipt.toml").unwrap();
        assert!(names.insert(stem.to_owned()));
        let raw = fs::read_to_string(&input).unwrap();
        assert!(raw.contains("[witness]\nschema_version = 1\n"));
        let key = format!("source-replayed-kernel-{stem}-5507a888eedd");
        let replaced = replace_header(&raw, "evidence_key", &key);
        let replaced = replace_header(&replaced, "expected_status", "source_only");
        let replaced = replace_header(&replaced, "applied_at", timestamp);
        let replaced = replace_header(
            &replaced,
            "reason",
            "Require internally-produced pinned Rocq source-closure compilation, exact retained object reproduction, independent kernel checking and complete declaration-assumption replay before active admission; retain all historical receipts.",
        );
        assert_eq!(
            raw.split_once("[witness]").unwrap().1,
            replaced.split_once("[witness]").unwrap().1,
            "witness bytes must remain identical",
        );
        let output = output_root.join(filename);
        fs::write(&output, replaced).unwrap();
        let digest = Command::new("sha256sum").arg(&output).output().unwrap();
        assert!(digest.status.success());
        let text = String::from_utf8(digest.stdout).unwrap();
        let hash = text.split_whitespace().next().unwrap();
        assert!(hash.len() == 64 && hash.chars().all(|value| value.is_ascii_hexdigit()));
        checksums.push_str(&format!("{hash}  {filename}\n"));
    }
    fs::write(output_root.join("SHA256SUMS"), checksums).unwrap();
    println!(
        "receipt_inputs=13\nexpected_source_only=13\nwitness_bytes=retained\noutput_directory=fresh"
    );
}
