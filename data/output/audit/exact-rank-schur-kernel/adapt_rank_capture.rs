use std::{fs,process::Command};
fn main(){
 let arguments:Vec<_>=std::env::args().collect(); assert_eq!(arguments.len(),3,"adapt REPOSITORY OUTPUT_SOURCE");
 let root=std::path::Path::new(&arguments[1]);
 let mut source=fs::read_to_string(root.join("data/output/audit/recorded-feedback-planned-look-coverage/capture_rocq_receipts.rs")).unwrap();
 source=source.replace("data/output/audit/recorded-feedback-planned-look-coverage/kernel-capture","data/output/audit/exact-rank-schur-kernel/kernel-capture");
 let targets=["StdlibRealFieldAdapter","RationalRealSpecialization","ExactRankCertificate","SchurKernelTransport","RecursiveCDTower","CDTowerMatrixAdapter","CDPureDoublingKernel","CDConcreteTowerAdapter","CDTowerFoldTransport","CDTowerSignCorrespondence","SedenionFoldTransport"];
 let start=source.find("const TARGETS:").unwrap(); let end=start+source[start..].find("];").unwrap()+2;
 let declaration=format!("const TARGETS: [&str; {}] = [{}];",targets.len(),targets.iter().map(|name|format!("\"theories/{name}.v\"")).collect::<Vec<_>>().join(", "));
 source.replace_range(start..end,&declaration);
 let hash=Command::new("sha256sum").arg(root.join("proofs/_RocqProject")).output().unwrap(); assert!(hash.status.success());
 let hash=String::from_utf8(hash.stdout).unwrap(); let hash=hash.split_whitespace().next().unwrap();
 source=source.replace("7d5e471e197045aa759e521a064f0cc28cef9fa33fe55e19b07c61ebe2023155",hash);
 let anchor="            let position = usize::from(matches!(";
 assert_eq!(source.matches(anchor).count(),1);
 source=source.replace(anchor,"            // Anonymous HB factories are compiled declarations without a queryable source name.\n            if words.starts_with(&[\"HB.instance\", \"Definition\", \"_\", \":=\"]) {\n                return None;\n            }\n            let position = usize::from(matches!(");
 fs::write(&arguments[2],source).unwrap();
}
