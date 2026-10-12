use std::{fs, path::Path};

fn main() {
    let arguments: Vec<_> = std::env::args().collect();
    assert_eq!(
        arguments.len(),
        4,
        "TEMPORARY_AUDIT NEW_RETAINED_DIRECTORY PRIVATE_CONTROL_DIRECTORY"
    );
    let source = Path::new(&arguments[1]);
    let destination = Path::new(&arguments[2]);
    fs::create_dir(destination).unwrap();
    for filename in [
        "determinism-audit.txt",
        "object-correspondence.tsv",
        "v2-source-review.txt",
    ] {
        let raw = fs::read_to_string(source.join(filename)).unwrap();
        let portable = raw.replace(&arguments[3], "private temporary interface-probe storage");
        for directory in ["home", "tmp", "root", "run/user", "var/tmp"] {
            let prefix = format!("/{directory}/");
            assert!(!portable.contains(&prefix), "local path in {filename}");
        }
        fs::write(destination.join(filename), portable).unwrap();
    }
    fs::write(destination.join("retention-note.txt"),
        "The independent temporary reports retain their analysis text and numeric witnesses. Portable publication replaces one temporary control-directory spelling with an explicit private-storage description. Raw compiler/checker logs, proof objects and ingested receipt inputs remain byte-identical. The companion admission passage identified by the source reviewer has been aligned with the v2 contract by the integration owner.\n").unwrap();
}
