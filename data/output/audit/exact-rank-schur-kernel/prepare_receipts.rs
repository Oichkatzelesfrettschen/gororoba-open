use std::{fs, path::Path, process::Command};
fn command_output(program: &str, arguments: &[&str]) -> Vec<u8> {
    let output = Command::new(program).args(arguments).output().unwrap();
    assert!(output.status.success(), "{program} failed");
    output.stdout
}
fn main() {
    let repository = std::env::args().nth(1).expect("repository root");
    let root = Path::new(&repository);
    let audit = root.join("data/output/audit/exact-rank-schur-kernel");
    let receipts = audit.join("receipts");
    fs::create_dir(&receipts).unwrap();
    let digest_output = command_output("sha256sum", &[root.join("proofs/_RocqProject").to_str().unwrap()]);
    let project_digest = std::str::from_utf8(&digest_output).unwrap().split_whitespace().next().unwrap();
    let timestamp = String::from_utf8(command_output("date", &["-u", "+%Y-%m-%dT%H:%M:%SZ"])).unwrap();
    let mut inputs = Vec::new();
    for entry in fs::read_dir(root.join("data/output/audit/recorded-feedback-planned-look-coverage/receipts")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|value| value == "toml") {
            let name = path.file_name().unwrap().to_str().unwrap().trim_end_matches(".receipt.toml").to_owned();
            if ["StdlibRealFieldAdapter", "RationalRealSpecialization", "ExactRankCertificate", "SchurKernelTransport", "RecursiveCDTower", "CDTowerMatrixAdapter", "CDPureDoublingKernel", "CDConcreteTowerAdapter", "CDTowerFoldTransport", "CDTowerSignCorrespondence", "SedenionFoldTransport"].contains(&name.as_str()) { continue; }
            let text = fs::read_to_string(&path).unwrap();
            inputs.push((name, text.split_once("[witness]\n").unwrap().1.to_owned()));
        }
    }
    for name in ["StdlibRealFieldAdapter", "RationalRealSpecialization", "ExactRankCertificate", "SchurKernelTransport", "RecursiveCDTower", "CDTowerMatrixAdapter", "CDPureDoublingKernel", "CDConcreteTowerAdapter", "CDTowerFoldTransport", "CDTowerSignCorrespondence", "SedenionFoldTransport"] {
        let text = fs::read_to_string(audit.join(format!("kernel-capture/witnesses/{name}.witness.toml"))).unwrap();
        let prefixed = text.lines().map(|line| {
            if let Some(body) = line.strip_prefix("[[") { format!("[[witness.{body}") }
            else if let Some(body) = line.strip_prefix('[') { format!("[witness.{body}") }
            else { line.to_owned() }
        }).collect::<Vec<_>>().join("\n");
        inputs.push((name.to_owned(), prefixed));
    }
    inputs.sort_by(|left, right| left.0.cmp(&right.0));
    for (name, witness) in &inputs {
        assert!(name.chars().all(|value| value.is_ascii_alphanumeric() || value == '_'));
        let query = format!("SELECT hex(kernel_result) FROM theorem_identities WHERE stable_id='THM-LEGACY-{name}'");
        let encoded = command_output("sqlite3", &[root.join("registry/canonical/control_plane.sqlite3").to_str().unwrap(), &query]);
        let encoded = std::str::from_utf8(&encoded).unwrap().trim();
        let bytes = (0..encoded.len()).step_by(2).map(|offset| u8::from_str_radix(&encoded[offset..offset+2], 16).unwrap()).collect::<Vec<_>>();
        let prestate = audit.join("kernel-prestate.tmp");
        fs::write(&prestate, bytes).unwrap();
        let hash_output = command_output("sha256sum", &[prestate.to_str().unwrap()]);
        let hash = std::str::from_utf8(&hash_output).unwrap().split_whitespace().next().unwrap();
        fs::remove_file(prestate).unwrap();
        let witness = witness.lines().map(|line| {
            if line.starts_with("project_sha256 =") { format!("project_sha256 = \"{project_digest}\"") }
            else { line.to_owned() }
        }).collect::<Vec<_>>().join("\n");
        let specification = format!("evidence_key = \"rank-kernel-project-{name}\"\nactor = \"chatgpt-codex\"\nreason = \"Replay source-bound compiler, kernel and assumptions against the extended project; preserve historical receipts.\"\napplied_at = \"{}\"\nexpected_kernel_result_sha256 = \"{hash}\"\nexpected_status = \"source_only\"\n\n[witness]\n{witness}\n", timestamp.trim());
        fs::write(receipts.join(format!("{name}.receipt.toml")), specification).unwrap();
    }
    println!("prepared_receipts={}", inputs.len());
}
