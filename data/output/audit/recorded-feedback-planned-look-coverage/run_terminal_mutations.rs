use std::{fs, path::Path, process::Command};
fn main() {
    let root = std::env::current_dir().unwrap();
    let scratch_arg = std::env::args().nth(1).expect("fresh scratch"); let scratch = Path::new(&scratch_arg);
    fs::create_dir(scratch).unwrap();
    let source = fs::read_to_string(root.join("proofs/theories/TerminalChannelEmpiricalCertificate.v")).unwrap();
    let cases = [
      ("missing-fourth-radius", "radius 0%nat + radius 1%nat + radius 2%nat + radius 3%nat)", "radius 0%nat + radius 1%nat + radius 2%nat)", 1),
      ("weakened-radius-failure", "if Rlt_dec (radius index) (Rabs (parameters index - center index sample)) then true else false.", "if Rlt_dec (2 * radius index) (Rabs (parameters index - center index sample)) then true else false.", 1),
      ("historical-count-damage", "| 0%nat => 2964 / 8192", "| 0%nat => 2965 / 8192", 1),
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
