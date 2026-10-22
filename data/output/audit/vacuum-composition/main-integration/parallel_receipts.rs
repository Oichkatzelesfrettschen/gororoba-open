use std::{fs, path::PathBuf, process::Command, sync::{Arc, Mutex}};

fn output(program: &str, arguments: &[&str]) -> Vec<u8> {
    let result = Command::new(program).args(arguments).output().unwrap();
    assert!(result.status.success(), "{program}: {}", String::from_utf8_lossy(&result.stderr));
    result.stdout
}

fn main() {
    let audit = PathBuf::from("data/output/audit/vacuum-composition/main-integration");
    let original = fs::read_to_string(audit.join("receipts/BooleanANFDegree.receipt.toml")).unwrap();
    let date_line = original.lines().find(|line| line.starts_with("applied_at =")).unwrap();
    let project_output = output("sha256sum", &["proofs/_RocqProject"]);
    let project = std::str::from_utf8(&project_output).unwrap().split_whitespace().next().unwrap();
    let mut inputs: Vec<PathBuf> = fs::read_dir("data/output/audit/exact-rank-schur-kernel/receipts").unwrap().map(|entry| entry.unwrap().path()).filter(|path| path.extension().is_some_and(|value| value == "toml")).collect();
    for name in ["PassiveMechanicalMemory", "FiniteComplexPassivity", "VacuumCounterexamples", "GaussianCoherence", "WorldlineInteraction", "VacuumSpectralModels", "FiniteCompositePassivity", "VacuumAnalyticLimits"] {
        inputs.push(PathBuf::from("data/output/audit/vacuum-composition/receipts").join(format!("{name}.receipt.toml")));
    }
    inputs.sort();
    assert_eq!(inputs.len(), 54);
    let mut pending = Vec::new();
    for historical in inputs {
        let name = historical.file_name().unwrap().to_str().unwrap().trim_end_matches(".receipt.toml");
        assert!(name.chars().all(|value| value.is_ascii_alphanumeric() || value == '_'));
        let destination = audit.join("receipts").join(format!("{name}.receipt.toml"));
        if !destination.exists() {
            let text = fs::read_to_string(&historical).unwrap();
            let witness = text.split_once("[witness]\n").unwrap().1.lines().map(|line| if line.starts_with("project_sha256 =") { format!("project_sha256 = \"{project}\"") } else { line.to_owned() }).collect::<Vec<_>>().join("\n");
            let query = format!("SELECT hex(kernel_result) FROM theorem_identities WHERE stable_id='THM-LEGACY-{name}'");
            let encoded = output("sqlite3", &["-readonly", "registry/canonical/control_plane.sqlite3", &query]);
            let encoded = std::str::from_utf8(&encoded).unwrap().trim();
            let bytes = (0..encoded.len()).step_by(2).map(|offset| u8::from_str_radix(&encoded[offset..offset+2],16).unwrap()).collect::<Vec<_>>();
            let temporary = audit.join("prestate.tmp");
            fs::write(&temporary, bytes).unwrap();
            let hash_output = output("sha256sum", &[temporary.to_str().unwrap()]);
            let digest = std::str::from_utf8(&hash_output).unwrap().split_whitespace().next().unwrap();
            fs::remove_file(temporary).unwrap();
            let specification = format!("evidence_key = \"vacuum-main-replay-{name}-{}\"\nactor = \"chatgpt-codex\"\nreason = \"Replay retained source, objects and declaration assumptions against combined main and vacuum project identity.\"\n{date_line}\nexpected_kernel_result_sha256 = \"{digest}\"\nexpected_status = \"source_only\"\n\n[witness]\n{witness}\n", &project[..12]);
            fs::write(&destination, specification).unwrap();
        }
        let event = format!("kernel-evidence:vacuum-main-replay-{name}-{}", &project[..12]);
        let query = format!("select count(*) from theorem_identity_events where binding_key='{event}'");
        let count = output("sqlite3", &["-readonly", "registry/canonical/control_plane.sqlite3", &query]);
        if std::str::from_utf8(&count).unwrap().trim() == "1" && audit.join("receipts").join(format!("{name}.log")).exists() {
            println!("retained_admission {name}");
        } else { pending.push(destination); }
    }
    let workers = std::thread::available_parallelism().unwrap().get();
    println!("native_workers={workers} pending_receipts={}",pending.len());
    let queue = Arc::new(Mutex::new(pending));
    let failures = Arc::new(Mutex::new(Vec::new()));
    std::thread::scope(|scope| {
        for _ in 0..workers {
            let queue = Arc::clone(&queue); let failures = Arc::clone(&failures); let audit = &audit;
            scope.spawn(move || loop {
                let Some(specification) = queue.lock().unwrap().pop() else { break; };
                let name = specification.file_stem().unwrap().to_str().unwrap();
                let replay = Command::new("opam").args(["exec","--switch=rocq-9.3","--","/tmp/exact_rank_gororoba_db","theorem","identity","record-kernel-evidence","--spec"]).arg(&specification).args(["--regen-toml","false"]).output().unwrap();
                let mut log = replay.stdout; log.extend(replay.stderr);
                fs::write(audit.join("receipts").join(format!("{name}.parallel.log")), &log).unwrap();
                println!("{name} exit {}", replay.status.code().unwrap_or(-1));
                if replay.status.success() { fs::write(audit.join("receipts").join(format!("{name}.log")), log).unwrap(); }
                else { failures.lock().unwrap().push(specification); }
            });
        }
    });
    let failures = failures.lock().unwrap();
    assert!(failures.is_empty(), "failed independent admissions: {failures:?}");
}
