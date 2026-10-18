use std::{fs, io::Write, path::Path, process::{Command,Stdio}};
fn main() {
    let arguments: Vec<_> = std::env::args().collect(); assert_eq!(arguments.len(),3);
    let source = Path::new(&arguments[1]); let root = Path::new(&arguments[2]);
    let commit = "2c94fbcb964596c130de9f94c3c8f583fd592c82";
    let inventory = fs::read_to_string(root.join("photonic-inputs/source-identities.sha256")).unwrap();
    let mut verified = 0;
    for line in inventory.lines() {
        let (expected,relative) = line.split_once("  ").unwrap();
        let blob = Command::new("git").arg("-C").arg(source).args(["show",&format!("{commit}:{relative}")]).output().unwrap();
        assert!(blob.status.success(),"source blob {relative}");
        let mut hash = Command::new("sha256sum").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        hash.stdin.take().unwrap().write_all(&blob.stdout).unwrap(); let result = hash.wait_with_output().unwrap();
        assert!(result.status.success()); let actual = String::from_utf8(result.stdout).unwrap();
        assert_eq!(actual.split_whitespace().next().unwrap(),expected,"published blob mismatch {relative}");
        verified += 1;
    }
    println!("published_source_commit={commit}\nverified_published_input_entries={verified}\nsource_and_destination_visibility=PUBLIC");
}
