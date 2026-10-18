//! Wrap genuine capture witnesses with read-only canonical metadata prestates.
//! Inventory synchronization preserves kernel_result bytes while recomputing
//! execution statuses. Admission therefore expects source_only after that sync.
use std::{
    fs::{self, OpenOptions},
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

fn quoted(value: &str) -> String {
    format!("\"{}\"", value.replace('\\', "\\\\").replace('"', "\\\""))
}
fn field(raw: &str, name: &str) -> String {
    let prefix = format!("{name} = \"");
    raw.lines()
        .find_map(|line| {
            line.strip_prefix(&prefix)
                .and_then(|value| value.strip_suffix('"'))
        })
        .unwrap_or_else(|| panic!("missing scalar field {name}"))
        .to_owned()
}
fn digest(bytes: &[u8]) -> String {
    let mut process = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    process.stdin.take().unwrap().write_all(bytes).unwrap();
    let result = process.wait_with_output().unwrap();
    assert!(result.status.success());
    String::from_utf8(result.stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned()
}
fn canonical_kernel_result(root: &Path, stable_id: &str) -> Vec<u8> {
    assert!(
        stable_id
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_'))
    );
    let result = Command::new("sqlite3")
        .arg("-readonly")
        .arg(root.join("registry/canonical/control_plane.sqlite3"))
        .arg(format!(
            "SELECT hex(kernel_result) FROM theorem_identities WHERE stable_id='{stable_id}';"
        ))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "read-only canonical metadata lookup failed"
    );
    let encoded = String::from_utf8(result.stdout).unwrap();
    let encoded = encoded.trim();
    assert_eq!(encoded.len() % 2, 0);
    (0..encoded.len())
        .step_by(2)
        .map(|offset| u8::from_str_radix(&encoded[offset..offset + 2], 16).unwrap())
        .collect()
}
fn main() {
    let arguments: Vec<_> = std::env::args().collect();
    assert_eq!(arguments.len(), 2, "usage: generate_receipts REPOSITORY");
    let root = Path::new(&arguments[1]);
    let directory = root.join("data/output/audit/vacuum-composition/receipts");
    let witnesses = root.join("data/output/audit/vacuum-composition/kernel-capture/witnesses");
    let timestamp = Command::new("date")
        .args(["-u", "+%Y-%m-%dT%H:%M:%SZ"])
        .output()
        .unwrap();
    assert!(timestamp.status.success());
    let applied_at = String::from_utf8(timestamp.stdout).unwrap();
    let applied_at = applied_at.trim();
    let mut files: Vec<_> = fs::read_dir(witnesses)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .ends_with(".witness.toml")
        })
        .collect();
    files.sort();
    assert_eq!(files.len(), 25);
    for path in files {
        let witness = fs::read_to_string(&path).unwrap();
        let stable_id = field(&witness, "stable_id");
        let project = field(&witness, "project_sha256");
        assert_eq!(project.len(), 64);
        assert_eq!(field(&witness, "toolchain"), "Rocq 9.3.0; OCaml 5.5.1");
        let stem = stable_id.strip_prefix("THM-LEGACY-").unwrap();
        let event_key = format!("vacuum-source-replay-{stem}-{}", &project[..12]);
        let prestate = digest(&canonical_kernel_result(root, &stable_id));
        let mut receipt = format!(
            "evidence_key = {}\nactor = \"codex\"\nreason = \"Record current-source Rocq 9.3.0 kernel execution and complete declaration assumptions; preserve mathematical model scope and physical residuals.\"\napplied_at = {}\nexpected_kernel_result_sha256 = {}\nexpected_status = \"source_only\"\n\n[witness]\n",
            quoted(&event_key),
            quoted(applied_at),
            quoted(&prestate)
        );
        for line in witness.lines() {
            if line.starts_with("[[") {
                receipt.push_str(&format!(
                    "[[witness.{}]]\n",
                    line.strip_prefix("[[").unwrap().strip_suffix("]]").unwrap()
                ));
            } else if line.starts_with('[') {
                receipt.push_str(&format!(
                    "[witness.{}]\n",
                    line.strip_prefix('[').unwrap().strip_suffix(']').unwrap()
                ));
            } else {
                receipt.push_str(line);
                receipt.push('\n');
            }
        }
        let destination = directory.join(format!("{stem}.receipt.toml"));
        let mut output = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&destination)
            .unwrap();
        output.write_all(receipt.as_bytes()).unwrap();
        println!(
            "generated {stable_id} expected_status=source_only kernel_result_sha256={prestate}"
        );
    }
}
