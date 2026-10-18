use serde_json::{Value, json};
use std::{fs, path::PathBuf, process::Command};
fn rational(numerator: i32, denominator: i32) -> Value {
 json!({"numerator":numerator.to_string(),"denominator":denominator.to_string()})
}
fn matrix(rows: usize, columns: usize, entries: Vec<Vec<Value>>) -> Value {
 json!({"rows":rows,"columns":columns,"entries":entries})
}
fn main() {
 let arguments: Vec<_> = std::env::args_os().collect();
 assert_eq!(arguments.len(),4,"boundary INGESTOR REPOSITORY FRESH_OUTPUT");
 let root=PathBuf::from(&arguments[2]); let output=PathBuf::from(&arguments[3]);
 fs::create_dir(&output).unwrap();
 for (name,rows,columns,rank) in [("empty",0,0,0),("zero_rank",2,2,0),("fraction",2,2,1),("full_rank",1,1,1)] {
  let mut fixture=json!({"schema":"exact-rank-kernel-v1","field":"rational","rows":rows,"columns":columns,"rank":rank});
  let width=columns-rank;
  for (field,height,breadth) in [("operator",rows,columns),("upper_left",rows,rank),("upper_right",rank,columns),("lower_left",rank,rows),("lower_right",columns,rank),("kernel",columns,width),("kernel_left_inverse",width,columns)] {
   let mut entries=vec![vec![rational(0,1);breadth];height];
   for (row,values) in entries.iter_mut().enumerate() { for (column,value) in values.iter_mut().enumerate() {
    let diagonal=row==column;
    *value=match field {
     "operator"|"upper_left" if diagonal && row<rank => rational(-2,3),
     "upper_right"|"lower_right" if diagonal => rational(1,1),
     "lower_left" if diagonal => rational(-3,2),
     "kernel" if row==column+rank => rational(1,1),
     "kernel_left_inverse" if column==row+rank => rational(1,1),
     _=>rational(0,1),
    };
   }}
   fixture[field]=matrix(height,breadth,entries);
  }
  let source=output.join(format!("{name}.json")); let proof=output.join(format!("{name}.v"));
  fs::write(&source,serde_json::to_vec_pretty(&fixture).unwrap()).unwrap();
  let ingestion=Command::new(&arguments[1]).arg(&source).arg(&proof).output().unwrap();
  assert!(ingestion.status.success(),"ingestion {name}: {}",String::from_utf8_lossy(&ingestion.stderr));
  let compilation=Command::new("opam").args(["exec","--switch=rocq-9.3","--","rocq","compile","-q","-w","+default","-Q"]).arg(root.join("proofs/theories")).arg("OpenGororoba").arg(&proof).output().unwrap();
  let mut log=compilation.stdout; log.extend(compilation.stderr); fs::write(output.join(format!("{name}.log")),&log).unwrap();
  assert!(compilation.status.success(),"compilation {name}: {}",String::from_utf8_lossy(&log));
  println!("{name}: rank and complete kernel proved");
 }
}
