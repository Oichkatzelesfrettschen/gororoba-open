use regex::Regex;

#[test]
fn genuine_rocq_replay_routes_owning_sources_and_build_inputs() {
    let workflow = include_str!("../../.github/workflows/ci.yml");
    let pattern = workflow
        .lines()
        .find_map(|line| {
            line.trim()
                .strip_prefix("proofs) pattern='")?
                .split_once('\'')
                .map(|value| value.0)
        })
        .expect("proofs component route");
    let route = Regex::new(pattern).expect("valid component regex");
    for path in [
        "proofs/theories/BooleanPermutation.v",
        "crates/provenance_store/src/theorem_execution.rs",
        "crates/provenance_store/src/theorem_replay.rs",
        "crates/provenance_store/Cargo.toml",
        "Cargo.toml",
        "Cargo.lock",
        "rust-toolchain.toml",
        ".cargo/config.toml",
        ".github/workflows/proofs.yml",
        ".github/workflows/ci.yml",
    ] {
        assert!(
            route.is_match(path),
            "genuine Rocq replay omitted for {path}"
        );
    }
    for path in ["docs/engineering/unrelated.txt", "crates/lbm_3d/src/lib.rs"] {
        assert!(!route.is_match(path), "unrelated path selected: {path}");
    }
}
