// SPDX-License-Identifier: MIT

//! A theorem mutation reads the proof tree, which `GOROROBA_MATH` names, and
//! opening the store creates its directory and applies migrations. With the
//! variable unset the command must stop before it touches the file system.

use std::{fs, process::Command};

#[test]
fn theorem_mutations_leave_no_file_when_the_proof_tree_is_unset() {
    let root = std::env::temp_dir().join(format!(
        "gororoba-db-unset-proof-tree-{}",
        std::process::id()
    ));
    fs::create_dir_all(&root).expect("create fixture root");
    let spec = root.join("spec.toml");
    fs::write(&spec, "").expect("write spec placeholder");
    for action in [
        "bind",
        "correct-links",
        "sync-inventory",
        "record-kernel-evidence",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_gororoba-db"))
            .env_remove("GOROROBA_MATH")
            .arg("--repo-root")
            .arg(&root)
            .args(["--db", "registry/canonical/control_plane.sqlite3"])
            .args(["theorem", "identity", action, "--spec"])
            .arg(&spec)
            .output()
            .expect("run gororoba-db");
        assert!(!output.status.success(), "{action} must fail");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("GOROROBA_MATH"), "{action}: {stderr}");
        let mut entries: Vec<_> = fs::read_dir(&root)
            .expect("read fixture root")
            .map(|entry| entry.expect("entry").file_name())
            .collect();
        entries.sort();
        assert_eq!(
            entries,
            ["spec.toml"],
            "{action} created files before the proof-tree check"
        );
    }
    fs::remove_file(&spec).expect("remove spec placeholder");
    fs::remove_dir(&root).expect("remove fixture root");
}
