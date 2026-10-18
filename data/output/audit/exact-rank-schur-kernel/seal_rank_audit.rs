use std::{fs,path::{Path,PathBuf},process::Command};
fn collect(directory:&Path, files:&mut Vec<PathBuf>){
 for entry in fs::read_dir(directory).unwrap(){
  let entry=entry.unwrap(); let kind=entry.file_type().unwrap();
  assert!(!kind.is_symlink(),"audit symlink");
  if kind.is_dir(){collect(&entry.path(),files)} else {assert!(kind.is_file()); files.push(entry.path());}
 }
}
fn main(){
 let argument=std::env::args().nth(1).expect("repository root");let root=Path::new(&argument);
 let audit=root.join("data/output/audit/exact-rank-schur-kernel");let manifest=audit.join("SHA256SUMS");
 let mut files=Vec::new();collect(&audit,&mut files);files.retain(|path|path!=&manifest);files.sort();
 let mut output=String::new();let mut bytes=0u64;
 for path in &files {
  let result=Command::new("sha256sum").arg(path).output().unwrap();assert!(result.status.success());
  let text=String::from_utf8(result.stdout).unwrap();let digest=text.split_whitespace().next().unwrap();
  output.push_str(&format!("{digest}  {}\n",path.strip_prefix(root).unwrap().display()));
  bytes+=fs::metadata(path).unwrap().len();
 }
 fs::write(manifest,output).unwrap();println!("sealed_files={}\nsealed_bytes={bytes}",files.len());
}
