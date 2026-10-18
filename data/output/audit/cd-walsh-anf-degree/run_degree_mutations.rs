use std::{fs, path::Path, process::Command};
fn main() {
    let root = std::env::current_dir().unwrap();
    let scratch = std::env::args().nth(1).expect("fresh scratch directory");
    let scratch = Path::new(&scratch);
    fs::create_dir(scratch).unwrap();
    let cases = [
        ("walsh-scale", "WalshProbability", "IZR (walsh order function frequency) ^ 2 / INR (Nat.pow 2 order) ^ 2.", "IZR (walsh order function frequency) ^ 2 / INR (Nat.pow 2 order)."),
        ("two-point-degree", "BooleanANFDegree", "right)) = order - 1.", "right)) = order."),
        ("zero-degree", "BooleanANFDegree", "anf_degree order (fun _ => false) = 0.", "anf_degree order (fun _ => false) = 1."),
        ("degree-noncancellation", "BooleanANFDegree", "anf_degree order first < anf_degree order second ->", "anf_degree order first <= anf_degree order second ->"),
        ("sign-row-degree", "CDPhaseDegree", "(sign_exponent (S (S extra)) left) = S extra.", "(sign_exponent (S (S extra)) left) = S (S extra)."),
        ("phase-first-appearance", "CDPhaseDegree", "Nat.max 1 (pair_first_order (S (S (S extra))) left middle - 2).", "Nat.max 1 (pair_first_order (S (S (S extra))) left middle - 1)."),
    ];
    for (label, module, before, after) in cases {
        let source = fs::read_to_string(root.join(format!("proofs/theories/{module}.v"))).unwrap();
        assert_eq!(source.matches(before).count(), 1, "mutation anchor {label}");
        let input = scratch.join("Mutation.v");
        fs::write(&input, source.replace(before, after)).unwrap();
        let output = Command::new("opam").args(["exec", "--switch=rocq-9.3", "--", "rocq", "compile", "-R"])
            .arg(root.join("proofs/theories")).args(["OpenGororoba", "-w", "+default"]).arg(&input).output().unwrap();
        let mut log = output.stdout;
        log.extend(output.stderr);
        let log_text = std::str::from_utf8(&log).unwrap();
        assert!(!output.status.success(), "mutation accepted: {label}");
        assert!(log_text.contains("Error:") && !log_text.contains("Cannot find a physical path"), "wrong failure: {label}");
        fs::write(root.join(format!("data/output/audit/cd-walsh-anf-degree/{label}.log")), log).unwrap();
        println!("{label}: rejected exit {}", output.status.code().unwrap());
    }
}
