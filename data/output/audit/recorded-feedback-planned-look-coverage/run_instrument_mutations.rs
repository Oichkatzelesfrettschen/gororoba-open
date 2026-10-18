use std::{fs, path::Path, process::Command};
fn main() {
    let root = std::env::current_dir().unwrap(); let scratch_arg = std::env::args().nth(1).expect("fresh scratch");
    let scratch = Path::new(&scratch_arg); fs::create_dir(scratch).unwrap();
    let cases = [
      ("wrong-feedback-bit", "RecordedFeedbackInstrument", "Definition recorded_feedback_branch density recorded := kraus_map (feedback recorded) (assigned_branch density recorded).", "Definition recorded_feedback_branch density recorded := kraus_map (feedback false) (assigned_branch density recorded).",1),
      ("wrong-work-basis", "FourStateMatrixAlgebra", "ket01 => 1%nat | ket10 => 2%nat", "ket01 => 2%nat | ket10 => 1%nat",1),
      ("asymmetric-bias-sign", "BranchSignedCoherence", "scale (one_to_zero-zero_to_one)", "scale (zero_to_one-one_to_zero)",3),
      ("asymmetric-common-mode", "BranchSignedCoherence", "scale (one_to_zero-zero_to_one)", "scale 0",3),
      ("wrong-column-readback", "FourStateMatrixAlgebra", "fun basis => vector (work_basis_index basis) (@fintype.ord0 0).", "fun basis => vector (work_basis_index ket00) (@fintype.ord0 0).",1),
      ("wrong-decoded-sign", "RecordedFeedbackInstrument", "law branch work_a work_b spectator * decoded_score (little_endian_word branch work_a work_b spectator)", "law branch work_a work_b spectator * (-decoded_score (little_endian_word branch work_a work_b spectator))",1),
      ("wrong-observed-imaginary-sign", "RecordedFeedbackInstrument", "((decoded_joint_score (laws PauliX PauliY) - decoded_joint_score (laws PauliY PauliX))/4)", "((decoded_joint_score (laws PauliY PauliX) - decoded_joint_score (laws PauliX PauliY))/4)",1),
      ("pauli-y-convention", "BranchSignedCoherence", "PauliY => if row then imaginary else negate imaginary", "PauliY => if row then negate imaginary else imaginary",1),
    ];
    for (label,module,before,after,count) in cases {
        let source = fs::read_to_string(root.join(format!("proofs/theories/{module}.v"))).unwrap();
        assert_eq!(source.matches(before).count(),count,"anchor {label}");
        let input = scratch.join("Mutation.v"); fs::write(&input,source.replace(before,after)).unwrap();
        let output = Command::new("opam").args(["exec","--switch=rocq-9.3","--","rocq","compile","-R"]).arg(root.join("proofs/theories")).args(["OpenGororoba","-w","+default"]).arg(input).output().unwrap();
        let mut log = output.stdout; log.extend(output.stderr); let text = std::str::from_utf8(&log).unwrap();
        assert!(!output.status.success() && text.contains("Error:") && !text.contains("Cannot find"),"mutation {label}");
        fs::write(root.join(format!("data/output/audit/recorded-feedback-planned-look-coverage/{label}.log")),log).unwrap();
        println!("{label}: rejected");
    }
}
