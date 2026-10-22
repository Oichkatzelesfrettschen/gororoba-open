use std::{fs, path::{Path, PathBuf}, process::Command};

fn output(program: &str, arguments: &[&str]) -> Vec<u8> {
    let result = Command::new(program).args(arguments).output().unwrap();
    assert!(result.status.success(), "{program}: {}", String::from_utf8_lossy(&result.stderr));
    result.stdout
}

fn main() {
    let root = std::env::current_dir().unwrap();
    let audit = root.join("data/output/audit/vacuum-composition/main-integration");
    fs::create_dir_all(audit.join("receipts")).unwrap();
    let project_output = output("sha256sum", &["proofs/_RocqProject"]);
    let project = std::str::from_utf8(&project_output).unwrap().split_whitespace().next().unwrap();
    let date_output = output("date", &["-u", "+%Y-%m-%dT%H:%M:%SZ"]);
    let date = std::str::from_utf8(&date_output).unwrap().trim();
    let database = "/tmp/exact_rank_gororoba_db";
    let inventory = format!("sync_key = \"vacuum-main-inventory-{project}\"\nactor = \"chatgpt-codex\"\nreason = \"Reconcile eight vacuum modules with main proof inventory and preserve append-only canonical history.\"\napplied_at = \"{date}\"\nproject_sha256 = \"{project}\"\n");
    fs::write(audit.join("inventory.toml"), inventory).unwrap();
    let result = output(database, &["theorem", "identity", "sync-inventory", "--spec", audit.join("inventory.toml").to_str().unwrap(), "--regen-toml", "false"]);
    fs::write(audit.join("inventory.log"), result).unwrap();
    let mut receipts: Vec<PathBuf> = fs::read_dir("data/output/audit/exact-rank-schur-kernel/receipts").unwrap().map(|entry| entry.unwrap().path()).filter(|path| path.extension().is_some_and(|value| value == "toml")).collect();
    for name in ["PassiveMechanicalMemory", "FiniteComplexPassivity", "VacuumCounterexamples", "GaussianCoherence", "WorldlineInteraction", "VacuumSpectralModels", "FiniteCompositePassivity", "VacuumAnalyticLimits"] {
        receipts.push(Path::new("data/output/audit/vacuum-composition/receipts").join(format!("{name}.receipt.toml")));
    }
    receipts.sort();
    assert_eq!(receipts.len(), 54);
    let mut failures = Vec::new();
    for (index, historical) in receipts.iter().enumerate() {
        let name = historical.file_name().unwrap().to_str().unwrap().trim_end_matches(".receipt.toml");
        assert!(name.chars().all(|value| value.is_ascii_alphanumeric() || value == '_'));
        let text = fs::read_to_string(historical).unwrap();
        let witness = text.split_once("[witness]\n").unwrap().1.lines().map(|line| if line.starts_with("project_sha256 =") { format!("project_sha256 = \"{project}\"") } else { line.to_owned() }).collect::<Vec<_>>().join("\n");
        let query = format!("SELECT hex(kernel_result) FROM theorem_identities WHERE stable_id='THM-LEGACY-{name}'");
        let prestate_hex = output("sqlite3", &["-readonly", "registry/canonical/control_plane.sqlite3", &query]);
        let prestate_hex = std::str::from_utf8(&prestate_hex).unwrap().trim();
        let prestate = (0..prestate_hex.len()).step_by(2).map(|offset| u8::from_str_radix(&prestate_hex[offset..offset + 2], 16).unwrap()).collect::<Vec<_>>();
        let temporary = audit.join("prestate.tmp");
        fs::write(&temporary, prestate).unwrap();
        let digest = output("sha256sum", &[temporary.to_str().unwrap()]);
        let digest = std::str::from_utf8(&digest).unwrap().split_whitespace().next().unwrap();
        fs::remove_file(temporary).unwrap();
        let specification = format!("evidence_key = \"vacuum-main-replay-{name}-{}\"\nactor = \"chatgpt-codex\"\nreason = \"Replay retained source, objects and declaration assumptions against combined main and vacuum project identity.\"\napplied_at = \"{date}\"\nexpected_kernel_result_sha256 = \"{digest}\"\nexpected_status = \"source_only\"\n\n[witness]\n{witness}\n", &project[..12]);
        let path = audit.join("receipts").join(format!("{name}.receipt.toml"));
        fs::write(&path, specification).unwrap();
        let replay = Command::new("opam").args(["exec", "--switch=rocq-9.3", "--", database, "theorem", "identity", "record-kernel-evidence", "--spec"]).arg(path).args(["--regen-toml", "false"]).output().unwrap();
        let mut log = replay.stdout;
        log.extend(replay.stderr);
        fs::write(audit.join("receipts").join(format!("{name}.log")), log).unwrap();
        println!("{}/54 {name} exit {}", index + 1, replay.status.code().unwrap_or(-1));
        if !replay.status.success() { failures.push(name.to_owned()); }
    }
    assert!(failures.is_empty(), "failed replays {failures:?}");
}
