use serde_json::Value;
use std::{fs, path::{Path, PathBuf}, process::Command};
fn copy_inputs(source: &Path, target: &Path) -> Vec<PathBuf> {
    let census = target.join("docs/evidence/box_kite_census/census.json");
    fs::create_dir_all(census.parent().unwrap()).unwrap();
    fs::copy(source.join("docs/evidence/box_kite_census/census.json"),census).unwrap();
    let original = source.join("results/quandela/cases/box_kite_photonic_single");
    let mut cases: Vec<_> = fs::read_dir(original).unwrap().map(|entry| entry.unwrap().path().join("cases.json")).filter(|path| path.is_file()).collect();
    cases.sort();
    let mut copied = Vec::new();
    for path in cases {
        let value: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        if value["blocks"].as_array().unwrap().iter().all(|block| block["kind"] != "two_label") { continue; }
        let relative = path.strip_prefix(source).unwrap(); let destination = target.join(relative);
        fs::create_dir_all(destination.parent().unwrap()).unwrap(); fs::copy(path,&destination).unwrap(); copied.push(destination);
    }
    assert_eq!(copied.len(),32); copied
}
fn write_json(path: &Path, value: &Value) { fs::write(path,serde_json::to_vec_pretty(value).unwrap()).unwrap(); }
fn main() {
    let arguments: Vec<_> = std::env::args().collect(); assert_eq!(arguments.len(),5);
    let source = Path::new(&arguments[1]); let helper = &arguments[2]; let scratch = Path::new(&arguments[3]); let repository = Path::new(&arguments[4]);
    fs::create_dir(scratch).unwrap();
    for mutation in ["ragged-matrix","invalid-sign","omitted-configuration","duplicate-configuration","damaged-witness"] {
        let root = scratch.join(mutation); let paths = copy_inputs(source,&root);
        let mut first: Value = serde_json::from_slice(&fs::read(&paths[0]).unwrap()).unwrap();
        match mutation {
            "ragged-matrix" => { first["blocks"][0]["m"][0].as_array_mut().unwrap().pop(); write_json(&paths[0],&first); }
            "invalid-sign" => { first["blocks"][0]["m"][0][0] = Value::from(0); write_json(&paths[0],&first); }
            "omitted-configuration" => { fs::rename(&paths[0],paths[0].with_extension("omitted")).unwrap(); }
            "duplicate-configuration" => {
                let mut second: Value = serde_json::from_slice(&fs::read(&paths[1]).unwrap()).unwrap();
                second["blocks"][0]["m"] = first["blocks"][0]["m"].clone(); second["blocks"][0]["t"] = first["blocks"][0]["t"].clone(); write_json(&paths[1],&second);
            }
            "damaged-witness" => { first["blocks"][0]["witness"] = serde_json::json!([1,2,1,1,2,1]); write_json(&paths[0],&first); }
            _ => unreachable!(),
        }
        let output = root.join("proposed"); let result = Command::new(helper).arg(&root).arg(&output).output().unwrap();
        let mut log = result.stdout; log.extend(result.stderr);
        if mutation == "damaged-witness" {
            assert!(result.status.success(),"damaged witness must reach Rocq's equation checker");
            let check = Command::new("opam").args(["exec","--switch=rocq-9.3","--","rocq","compile","-R"]).arg(repository.join("proofs/theories")).args(["OpenGororoba","-w","+default"]).arg(output.join("SparsePhotonicCertificates.v")).output().unwrap();
            assert!(!check.status.success()); let text = String::from_utf8_lossy(&check.stderr); assert!(text.contains("Error:") && !text.contains("Cannot find"));
            log.extend(check.stdout); log.extend(check.stderr);
        } else { assert!(!result.status.success(),"ingestor accepted {mutation}"); }
        fs::write(repository.join(format!("data/output/audit/cd-associator-census-transport/{mutation}.log")),log).unwrap();
        println!("{mutation}: rejected");
    }
}
