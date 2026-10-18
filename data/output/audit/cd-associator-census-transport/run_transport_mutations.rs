use std::{fs, path::Path, process::Command};
fn main() {
    let root = std::env::current_dir().unwrap();
    let scratch_arg = std::env::args().nth(1).expect("fresh scratch directory");
    let scratch = Path::new(&scratch_arg); fs::create_dir(scratch).unwrap();
    let cases = [
        ("census-denominator", "CDAssociatorCensus", "+ 6)) / 2.", "+ 6)) / 3."),
        ("photonic-normalization", "CDSparseBlockTransport", "two_label_squared_norm (two_label_output first second third fourth input_sign) / 8.", "two_label_squared_norm (two_label_output first second third fourth input_sign) / 4."),
        ("full-product-norm", "CDSparseBlockTransport", "two_label_squared_norm (two_label_output (IZR (phase_sign (sign_exponent order left lower)))", "2 * two_label_squared_norm (two_label_output (IZR (phase_sign (sign_exponent order left lower)))"),
        ("missing-output-coordinate", "CDSparseBlockTransport", "Definition two_blade_decoder order (first second : cube order) (index : fintype.ordinal 2) :=\n  cube_matrix_index order (if Nat.eqb (fintype.nat_of_ord index) 0 then first else second).", "Definition two_blade_decoder order (first second : cube order) (index : fintype.ordinal 2) :=\n  cube_matrix_index order (if Nat.eqb (fintype.nat_of_ord index) 0 then first else first)."),
        ("omitted-sector", "CDSparseBlockTransport", "cube_squared_norm order (sector_projection order group sector vector) else 0.", "cube_squared_norm order (sector_projection order group sector vector) else 1."),
    ];
    for (label, module, before, after) in cases {
        let source = fs::read_to_string(root.join(format!("proofs/theories/{module}.v"))).unwrap();
        assert_eq!(source.matches(before).count(),1,"anchor {label}");
        let input = scratch.join("Mutation.v"); fs::write(&input,source.replace(before,after)).unwrap();
        let output = Command::new("opam").args(["exec","--switch=rocq-9.3","--","rocq","compile","-R"]).arg(root.join("proofs/theories")).args(["OpenGororoba","-w","+default"]).arg(input).output().unwrap();
        let mut log = output.stdout; log.extend(output.stderr);
        let text = std::str::from_utf8(&log).unwrap();
        assert!(!output.status.success(),"accepted {label}");
        assert!(text.contains("Error:") && !text.contains("Cannot find"),"wrong failure {label}");
        fs::write(root.join(format!("data/output/audit/cd-associator-census-transport/{label}.log")),log).unwrap();
        println!("{label}: rejected");
    }
}
