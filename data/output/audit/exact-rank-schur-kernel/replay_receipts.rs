use std::{fs, path::PathBuf, process::Command};
fn main() {
    let root = std::env::current_dir().unwrap();
    let audit = root.join("data/output/audit/exact-rank-schur-kernel");
    let database = std::env::args().nth(1).expect("current-source gororoba-db executable");
    let mut specifications: Vec<PathBuf> = fs::read_dir(audit.join("receipts")).unwrap()
        .map(|entry| entry.unwrap().path()).filter(|path| path.extension().is_some_and(|extension| extension == "toml")).collect();
    specifications.sort(); assert_eq!(specifications.len(),46);
    let mut failures = Vec::new();
    for (index, specification) in specifications.iter().enumerate() {
        let output = Command::new("opam").args(["exec","--switch=rocq-9.3","--"])
            .arg(&database).arg("--repo-root").arg(&root)
            .args(["theorem","identity","record-kernel-evidence","--spec"])
            .arg(specification).args(["--regen-toml","false"]).output().unwrap();
        let mut log = output.stdout; log.extend(output.stderr);
        let name = specification.file_stem().unwrap().to_str().unwrap();
        fs::write(audit.join("receipts").join(format!("{name}.log")),log).unwrap();
        println!("{}/46 {} exit {}",index+1,name,output.status.code().unwrap_or(-1));
        if !output.status.success() { failures.push(name.to_owned()); }
    }
    assert!(failures.is_empty(),"failed receipt replays: {failures:?}");
}
