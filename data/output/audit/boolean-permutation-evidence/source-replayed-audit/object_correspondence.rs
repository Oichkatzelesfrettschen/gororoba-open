use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
    process::Command,
};

const TARGETS: [&str; 13] = [
    "theories/BooleanPermutation.v",
    "theories/FoldAverageDescent.v",
    "theories/TerminalChannelSeparation.v",
    "theories/TerminalChannelSeparationReal.v",
    "theories/SignCodeProjection.v",
    "theories/SchreierSignCode.v",
    "theories/SignCodeCardinality.v",
    "theories/BooleanCochainFiltration.v",
    "theories/SedenionMembershipConstraints.v",
    "theories/MinimalUncurvedObstruction.v",
    "verified/C958_ZDGraphTopology.v",
    "verified/C958b_ZDAdjacencyAnalytical.v",
    "verified/C1463_ArithmeticInventory.v",
];
const ARTIFACT: &str = "data/output/audit/boolean-permutation-evidence/complete-declaration-kernel";

fn digest(path: &Path) -> String {
    let output = Command::new("sha256sum").arg(path).output().unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout)
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned()
}

fn quoted(block: &str, key: &str) -> String {
    let prefix = format!("{key} = \"");
    let matches = block
        .lines()
        .filter_map(|line| line.strip_prefix(&prefix))
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "missing or repeated field {key}");
    matches[0].strip_suffix('"').unwrap().to_owned()
}

fn table<'a>(raw: &'a str, name: &str) -> &'a str {
    let marker = format!("[{name}]\n");
    raw.split_once(&marker)
        .unwrap()
        .1
        .split("\n[")
        .next()
        .unwrap()
}

fn dependencies(source: &str) -> &'static [&'static str] {
    match source {
        "theories/CayleyDicksonAlgebra.v" => &["theories/Prelude.v"],
        "theories/Sedenion.v" => &["theories/Prelude.v", "theories/CayleyDicksonAlgebra.v"],
        "theories/MinimalUncurvedObstruction.v" | "theories/SedenionMembershipConstraints.v" => {
            &["theories/CayleyDicksonAlgebra.v", "theories/Sedenion.v"]
        }
        "theories/SignCodeCardinality.v" => &["theories/SchreierSignCode.v"],
        "verified/C958_ZDGraphTopology.v" => &["theories/Prelude.v"],
        "verified/C958b_ZDAdjacencyAnalytical.v" => &["verified/C958_ZDGraphTopology.v"],
        _ => &[],
    }
}

fn order(source: &str, seen: &mut BTreeSet<String>, result: &mut Vec<String>) {
    if !seen.insert(source.to_owned()) {
        return;
    }
    for dependency in dependencies(source) {
        order(dependency, seen, result);
    }
    result.push(source.to_owned());
}

fn module(source: &str) -> String {
    let (directory, name) = source.split_once('/').unwrap();
    let namespace = match directory {
        "theories" => "OpenGororoba",
        "verified" => "OpenGororobaVerified",
        _ => panic!("unexpected source root"),
    };
    format!("{namespace}.{}", name.strip_suffix(".v").unwrap())
}

fn checked_local(root: &Path, relative: &str) -> PathBuf {
    assert!(
        Path::new(relative)
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
    );
    let path = root.join(relative);
    assert!(fs::symlink_metadata(&path).unwrap().file_type().is_file());
    path
}

fn run(pin: &Path, work: &Path, arguments: &[&str], log: &Path) -> i32 {
    let prefix = format!("{}:{}", pin.display(), std::env::var("PATH").unwrap());
    let output = Command::new(pin.join("rocq"))
        .env("PATH", prefix)
        .current_dir(work)
        .args(arguments)
        .output()
        .unwrap();
    let mut log_bytes = output.stdout;
    log_bytes.extend(output.stderr);
    fs::write(log, log_bytes).unwrap();
    output.status.code().unwrap_or(-1)
}

fn main() {
    let arguments = std::env::args().collect::<Vec<_>>();
    assert_eq!(arguments.len(), 4);
    let root = Path::new(&arguments[1]);
    let scratch = Path::new(&arguments[2]);
    let pin = Path::new(&arguments[3]);
    let artifact = root.join(ARTIFACT);
    assert_eq!(
        digest(&root.join("proofs/_RocqProject")),
        "5507a888eedd0cb8da4e5414d0882416b1bdcec0d1934fd9b87b189867e883b8"
    );
    let version = Command::new(pin.join("rocq"))
        .arg("--version")
        .output()
        .unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout.clone()).unwrap().trim(),
        "The Rocq Prover, version 9.1.1\ncompiled with OCaml 5.4.0"
    );
    fs::write(scratch.join("toolchain.txt"), version.stdout).unwrap();
    let mut retained_before = BTreeMap::new();
    let mut source_before = BTreeMap::new();
    let mut rows = String::from(
        "target\tcompile_order\tcompile_exit\tkernel_exit\tretained_sha256\tfresh_sha256\tresult\n",
    );
    let mut matching = BTreeSet::new();
    let mut mismatching = BTreeSet::new();
    let closure_tsv = fs::read_to_string(artifact.join("source-closures.tsv")).unwrap();
    let receipt_files = fs::read_dir(artifact.join("receipts"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .ends_with(".receipt.toml")
        })
        .collect::<Vec<_>>();
    assert_eq!(receipt_files.len(), TARGETS.len());
    for target in TARGETS {
        let name = Path::new(target).file_stem().unwrap().to_str().unwrap();
        let receipt_path = artifact
            .join("receipts")
            .join(format!("{name}.receipt.toml"));
        retained_before.insert(receipt_path.clone(), digest(&receipt_path));
        let raw = fs::read_to_string(&receipt_path).unwrap();
        let witness = table(&raw, "witness");
        assert_eq!(quoted(witness, "proof_path"), format!("proofs/{target}"));
        assert_eq!(quoted(witness, "warning_policy"), "fatal_default");
        assert_eq!(quoted(witness, "toolchain"), "Rocq 9.1.1; OCaml 5.4.0");
        assert_eq!(
            quoted(witness, "project_sha256"),
            digest(&root.join("proofs/_RocqProject"))
        );
        assert_eq!(
            quoted(witness, "compile_command"),
            format!(
                "rocq compile -q -w +default -R theories OpenGororoba -R verified OpenGororobaVerified {target}"
            )
        );
        assert_eq!(
            quoted(witness, "kernel_command"),
            format!(
                "rocq check -silent -o -R theories OpenGororoba -R verified OpenGororobaVerified {}",
                module(target)
            )
        );
        let sources = raw
            .split("[[witness.sources]]\n")
            .skip(1)
            .map(|part| {
                let block = part.split("\n[").next().unwrap();
                (quoted(block, "path"), quoted(block, "sha256"))
            })
            .collect::<BTreeMap<_, _>>();
        let tsv_sources = closure_tsv
            .lines()
            .filter_map(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                assert_eq!(fields.len(), 3);
                (fields[0] == format!("proofs/{target}"))
                    .then(|| (fields[1].to_owned(), fields[2].to_owned()))
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(sources, tsv_sources);
        let mut ordered = Vec::new();
        let mut seen = BTreeSet::new();
        order(target, &mut seen, &mut ordered);
        assert_eq!(
            sources.keys().cloned().collect::<BTreeSet<_>>(),
            seen.iter()
                .map(|source| format!("proofs/{source}"))
                .collect()
        );
        let work = scratch.join(name).join("proofs");
        fs::create_dir_all(work.join("theories")).unwrap();
        fs::create_dir_all(work.join("verified")).unwrap();
        fs::copy(root.join("proofs/_RocqProject"), work.join("_RocqProject")).unwrap();
        for source in &ordered {
            let relative = format!("proofs/{source}");
            let original = checked_local(root, &relative);
            let original_digest = digest(&original);
            assert_eq!(original_digest, sources[&relative]);
            source_before.insert(original.clone(), original_digest);
            fs::copy(original, work.join(source)).unwrap();
            assert_eq!(digest(&work.join(source)), sources[&relative]);
        }
        let retained = table(&raw, "witness.proof_object");
        let retained_path = checked_local(root, &quoted(retained, "path"));
        let retained_digest = digest(&retained_path);
        assert_eq!(retained_digest, quoted(retained, "sha256"));
        retained_before.insert(retained_path, retained_digest.clone());
        let mut compile_exit = 0;
        for source in &ordered {
            let source_name = Path::new(source).file_stem().unwrap().to_str().unwrap();
            let status = run(
                pin,
                &work,
                &[
                    "compile",
                    "-q",
                    "-w",
                    "+default",
                    "-R",
                    "theories",
                    "OpenGororoba",
                    "-R",
                    "verified",
                    "OpenGororobaVerified",
                    source,
                ],
                &scratch
                    .join(name)
                    .join(format!("{source_name}.compile.txt")),
            );
            assert_eq!(status, 0, "compile {target} dependency {source}");
            compile_exit = status;
        }
        let logical = module(target);
        let kernel_log = scratch.join(name).join("kernel.txt");
        let kernel_exit = run(
            pin,
            &work,
            &[
                "check",
                "-silent",
                "-o",
                "-R",
                "theories",
                "OpenGororoba",
                "-R",
                "verified",
                "OpenGororobaVerified",
                &logical,
            ],
            &kernel_log,
        );
        assert_eq!(kernel_exit, 0, "kernel check {target}");
        assert!(
            fs::read_to_string(&kernel_log)
                .unwrap()
                .contains("CONTEXT SUMMARY")
        );
        let fresh_object = work.join(target).with_extension("vo");
        assert!(fs::read(&fresh_object).unwrap().starts_with(b"Coq!"));
        let fresh_digest = digest(&fresh_object);
        let result = if retained_digest == fresh_digest {
            matching.insert(target.to_owned());
            "match"
        } else {
            mismatching.insert(target.to_owned());
            "mismatch"
        };
        rows.push_str(&format!("{target}\t{}\t{compile_exit}\t{kernel_exit}\t{retained_digest}\t{fresh_digest}\t{result}\n", ordered.join(" -> ")));
        fs::write(scratch.join("object-correspondence.tsv"), &rows).unwrap();
        println!("{target}: {result}; closure {}", ordered.join(" -> "));
    }
    for (path, before) in retained_before.iter().chain(&source_before) {
        assert_eq!(
            &digest(path),
            before,
            "audited input changed: {}",
            path.display()
        );
    }
    assert_eq!(matching.len() + mismatching.len(), TARGETS.len());
    fs::write(scratch.join("summary.txt"), format!("target_count={}\nmatching_count={}\nmismatching_count={}\nretained_receipt_and_object_count={}\nsource_file_count={}\n", TARGETS.len(), matching.len(), mismatching.len(), retained_before.len(), source_before.len())).unwrap();
    println!(
        "denominator {}; matching {}; mismatching {}; retained inputs {} unchanged; source inputs {} unchanged",
        TARGETS.len(),
        matching.len(),
        mismatching.len(),
        retained_before.len(),
        source_before.len()
    );
    println!("audit_root={}", scratch.display());
    assert!(mismatching.is_empty(), "object byte correspondence failed");
}
