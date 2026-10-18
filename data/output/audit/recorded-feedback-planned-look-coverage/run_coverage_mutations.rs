use std::{fs, path::Path, process::Command};
fn main() {
    let root = std::env::current_dir().unwrap();
    let scratch_arg = std::env::args().nth(1).expect("fresh scratch"); let scratch = Path::new(&scratch_arg);
    fs::create_dir(scratch).unwrap();
    let source = fs::read_to_string(root.join("proofs/theories/FinitePlannedLookCoverage.v")).unwrap();
    let cases = [
      ("omitted-look-selection", "(forall sample pair, selection sample = Some pair -> In pair declared) ->", "(forall sample pair, selection sample = Some pair -> True) ->", 2),
      ("missing-marginal-coverage", "event_probability law (failure pair) <= allocation pair", "event_probability law (failure pair) <= allocation pair + 1", 3),
      ("wrong-total-budget", "real_sum (map allocation declared) <= total_budget", "real_sum (map allocation declared) <= total_budget + 1", 3),
    ];
    for (label,before,after,count) in cases {
        assert_eq!(source.matches(before).count(),count,"anchor {label}");
        let input = scratch.join("Mutation.v"); fs::write(&input,source.replace(before,after)).unwrap();
        let output = Command::new("opam").args(["exec","--switch=rocq-9.3","--","rocq","compile","-R"]).arg(root.join("proofs/theories")).args(["OpenGororoba","-w","+default"]).arg(input).output().unwrap();
        let mut log = output.stdout; log.extend(output.stderr); let text = std::str::from_utf8(&log).unwrap();
        assert!(!output.status.success() && text.contains("Error:") && !text.contains("Cannot find"),"mutation {label}");
        fs::write(root.join(format!("data/output/audit/recorded-feedback-planned-look-coverage/{label}.log")),log).unwrap();
        println!("{label}: rejected");
    }
}
