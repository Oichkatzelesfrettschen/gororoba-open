use std::{fs, path::PathBuf, process::Command};
fn main() {
 let arguments: Vec<_> = std::env::args_os().collect();
 assert_eq!(arguments.len(),3,"mutations REPOSITORY FRESH_OUTPUT");
 let root=PathBuf::from(&arguments[1]); let output=PathBuf::from(&arguments[2]); fs::create_dir(&output).unwrap();
 let cases=[
 ("skew_minus","SchurKernelTransport","trailing + (trmx upper) *m pivot_inverse *m upper","trailing - (trmx upper) *m pivot_inverse *m upper"),
 ("lift_sign","SchurKernelTransport","col_mx (- (pivot_inverse *m upper *m vector)) vector","col_mx (pivot_inverse *m upper *m vector) vector"),
 ("gram_sign","SchurKernelTransport","1%:M + trmx (pivot_inverse *m upper)","1%:M - trmx (pivot_inverse *m upper)"),
 ("conjugacy_sign","CDPureDoublingKernel","tower_right_matrix order operand = nmodule.Algebra.opp","tower_right_matrix order operand = (fun value => value)"),
 ("fold_scale","CDTowerFoldTransport","= (1/2) * tower_norm_sq (S order) value","= 2 * tower_norm_sq (S order) value"),
 ("boolean_sign","CDTowerSignCorrespondence","if negative then tower_neg order value else value","if negative then value else tower_neg order value"),
 ("highest_bit","CDTowerSignCorrespondence","then (tower_zero lower,tower_basis lower (fst value))","then (tower_basis lower (fst value),tower_zero lower)"),
 ];
 for (name,module,original,altered) in cases {
  let source=fs::read_to_string(root.join(format!("proofs/theories/{module}.v"))).unwrap();
  assert_eq!(source.matches(original).count(),1,"unique mutation anchor {name}");
  let target=output.join(format!("{name}.v")); fs::write(&target,source.replacen(original,altered,1)).unwrap();
  let result=Command::new("opam").args(["exec","--switch=rocq-9.3","--","rocq","compile","-q","-w","+default","-Q"]).arg(root.join("proofs/theories")).arg("OpenGororoba").arg(&target).output().unwrap();
  let mut log=result.stdout; log.extend(result.stderr); let diagnostic=String::from_utf8_lossy(&log);
  assert!(!result.status.success(),"{name} must reject altered law");
  assert!(diagnostic.contains("Error:") && !diagnostic.contains("Unable to locate") && !diagnostic.contains("inconsistent assumptions"),"{name} must reject law rather than dependency: {diagnostic}");
  fs::write(output.join(format!("{name}.log")),log).unwrap(); println!("{name}: rejected");
 }
}
