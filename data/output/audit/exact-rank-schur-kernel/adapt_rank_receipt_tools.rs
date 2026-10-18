use std::{fs,path::Path};
fn main(){
 let argument=std::env::args().nth(1).expect("repository root"); let root=Path::new(&argument);
 let old=root.join("data/output/audit/recorded-feedback-planned-look-coverage");
 let new=root.join("data/output/audit/exact-rank-schur-kernel");
 let names=["StdlibRealFieldAdapter","RationalRealSpecialization","ExactRankCertificate","SchurKernelTransport","RecursiveCDTower","CDTowerMatrixAdapter","CDPureDoublingKernel","CDConcreteTowerAdapter","CDTowerFoldTransport","CDTowerSignCorrespondence","SedenionFoldTransport"];
 let list=format!("[{}]",names.iter().map(|name|format!("\"{name}\"")).collect::<Vec<_>>().join(", "));
 let previous="[\"FinitePlannedLookCoverage\", \"FourStateMatrixAlgebra\", \"RecordedFeedbackInstrument\", \"BranchSignedCoherence\", \"TerminalChannelEmpiricalCertificate\"]";
 let mut prepare=fs::read_to_string(old.join("prepare_receipts.rs")).unwrap();
 assert_eq!(prepare.matches(previous).count(),2);
 prepare=prepare.replace("let audit = root.join(\"data/output/audit/recorded-feedback-planned-look-coverage\")","let audit = root.join(\"data/output/audit/exact-rank-schur-kernel\")")
 .replace("data/output/audit/cd-associator-census-transport/receipts","data/output/audit/recorded-feedback-planned-look-coverage/receipts")
 .replace(previous,&list).replace("feedback-coverage-project-","rank-kernel-project-");
 fs::write(new.join("prepare_receipts.rs"),prepare).unwrap();
 let replay=fs::read_to_string(old.join("replay_receipts.rs")).unwrap().replace("data/output/audit/recorded-feedback-planned-look-coverage","data/output/audit/exact-rank-schur-kernel").replace("len(),36","len(),46").replace("{}/36","{}/46");
 fs::write(new.join("replay_receipts.rs"),replay).unwrap();
}
