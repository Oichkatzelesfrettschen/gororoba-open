use serde_json::{Value,json};
use std::{fs,path::PathBuf,process::Command};
fn main() {
 let arguments: Vec<_> = std::env::args_os().collect();
 assert_eq!(arguments.len(),5,"mutation FIXTURE INGESTOR REPOSITORY FRESH_SCRATCH");
 let fixture: Value = serde_json::from_slice(&fs::read(&arguments[1]).unwrap()).unwrap();
 let root=PathBuf::from(&arguments[3]); let scratch=PathBuf::from(&arguments[4]); fs::create_dir(&scratch).unwrap();
 let cases=[("ragged-matrix",true),("incorrect-field",true),("zero-denominator",true),("incompatible-dimensions",true),("incomplete-frame",true),
 ("damaged-upper-factor",false),("damaged-lower-witness",false),("damaged-kernel-residual",false),("damaged-independence-witness",false)];
 for (name, ingestion_rejects) in cases {
  let mut damaged=fixture.clone();
  match name {
   "ragged-matrix"=>damaged["operator"]["entries"][0]=json!([]),
   "incorrect-field"=>damaged["field"]=json!("float64"),
   "zero-denominator"=>damaged["operator"]["entries"][0][0]["denominator"]=json!("0"),
   "incompatible-dimensions"=>damaged["upper_left"]["rows"]=json!(1),
   "incomplete-frame"=>damaged["kernel"]["columns"]=json!(0),
   "damaged-upper-factor"=>damaged["upper_left"]["entries"][0][0]["numerator"]=json!("2"),
   "damaged-lower-witness"=>damaged["lower_left"]["entries"][0][0]["numerator"]=json!("0"),
   "damaged-kernel-residual"=>damaged["kernel"]["entries"][0][0]["numerator"]=json!("1"),
   "damaged-independence-witness"=>damaged["kernel_left_inverse"]["entries"][0][1]["numerator"]=json!("0"),
   _=>unreachable!(),
  }
  let source=scratch.join(format!("{name}.json")); let proof=scratch.join(format!("{}.v",name.replace('-',"_")));
  fs::write(&source,serde_json::to_vec_pretty(&damaged).unwrap()).unwrap();
  let ingestion=Command::new(&arguments[2]).arg(&source).arg(&proof).output().unwrap();
  let mut log=ingestion.stdout; log.extend(ingestion.stderr);
  if ingestion_rejects { assert!(!ingestion.status.success(),"{name} must reject ingestion"); }
  else {
   assert!(ingestion.status.success(),"{name} must reach mathematical checking");
   let compilation=Command::new("opam").args(["exec","--switch=rocq-9.3","--","rocq","compile","-q","-w","+default","-R"])
     .arg(root.join("proofs/theories")).arg("OpenGororoba").arg(&proof).output().unwrap();
   assert!(!compilation.status.success(),"{name} must reject damaged equations");
   assert!(String::from_utf8_lossy(&compilation.stderr).contains("Error:"),"{name} must reach a Rocq error");
   log.extend(compilation.stdout); log.extend(compilation.stderr);
  }
  fs::write(scratch.join(format!("{name}.log")),log).unwrap(); println!("{name}: rejected");
 }
}
