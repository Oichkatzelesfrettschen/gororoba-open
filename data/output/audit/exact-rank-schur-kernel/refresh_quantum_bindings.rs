use serde_json::Value;
use provenance_store::quantum_bindings::QuantumBindingManifest;
use std::{collections::{BTreeMap,BTreeSet}, fs, io::Write, path::Path, process::{Command,Stdio}};
fn digest(bytes: &[u8]) -> String {
    let mut child = Command::new("sha256sum").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(bytes).unwrap(); let output = child.wait_with_output().unwrap(); assert!(output.status.success());
    String::from_utf8(output.stdout).unwrap().split_whitespace().next().unwrap().to_owned()
}
fn main() {
    let argument = std::env::args().nth(1).expect("repository root"); let root = Path::new(&argument);
    let path = root.join("proofs/evidence/quantum_observables/bindings.json");
    let prestate = std::env::args().nth(2).map(std::path::PathBuf::from).unwrap_or_else(|| path.clone());
    let mut manifest: Value = serde_json::from_slice(&fs::read(&prestate).unwrap()).unwrap();
    let original_order: Vec<_> = manifest["theorems"].as_array().unwrap().iter().map(|binding| (binding["source"].as_str().unwrap().to_owned(), binding["declaration"].as_str().unwrap().to_owned())).collect();
    let original_assets = manifest["assets"].clone(); let original_application = manifest["coherence_application"].clone();
    let originals: BTreeMap<_,_> = manifest["theorems"].as_array().unwrap().iter().map(|binding|
      ((binding["source"].as_str().unwrap().to_owned(),binding["declaration"].as_str().unwrap().to_owned()),binding.clone())).collect();
    let mut sources: BTreeSet<_> = originals.keys().map(|(source,_)|source.clone()).collect();
    sources.extend(["FinitePlannedLookCoverage","FourStateMatrixAlgebra","RecordedFeedbackInstrument"].map(|name|format!("proofs/theories/{name}.v")));
    let mut renewed = Vec::new();
    for source in &sources {
        let bytes = fs::read(root.join(source)).unwrap(); let identity = digest(&bytes); let text = std::str::from_utf8(&bytes).unwrap();
        let template_source = if source.ends_with("FinitePlannedLookCoverage.v") { "proofs/theories/FiniteProbability.v" }
          else if source.ends_with("FourStateMatrixAlgebra.v") || source.ends_with("RecordedFeedbackInstrument.v") { "proofs/theories/BranchSignedCoherence.v" }
          else { source.as_str() };
        let template = originals.iter().find(|((candidate,_),_)| candidate == template_source).unwrap().1;
        for line in text.lines().map(str::trim_start) {
            for prefix in ["Theorem ","Lemma ","Corollary "] {
                if let Some(tail) = line.strip_prefix(prefix) {
                    let declaration: String = tail.chars().take_while(|character|character.is_ascii_alphanumeric() || *character == '_').collect(); assert!(!declaration.is_empty());
                    let mut binding = originals.get(&(source.clone(),declaration.clone())).unwrap_or(template).clone();
                    binding["source"] = Value::from(source.clone()); binding["sha256"] = Value::from(identity.clone()); binding["declaration"] = Value::from(declaration);
                    assert_eq!(binding["execution"],"mathematical_only"); assert!(binding["decoder_members"].as_array().unwrap().is_empty());
                    renewed.push(binding);
                }
            }
        }
        assert_eq!(fs::read(root.join(source)).unwrap(),bytes,"source changed while freezing {source}");
    }
    renewed.sort_by(|left,right| (left["source"].as_str().unwrap(),left["declaration"].as_str().unwrap()).cmp(&(right["source"].as_str().unwrap(),right["declaration"].as_str().unwrap())));
    let mut remaining: BTreeMap<_,_> = renewed.into_iter().map(|binding| ((binding["source"].as_str().unwrap().to_owned(),binding["declaration"].as_str().unwrap().to_owned()),binding)).collect();
    let mut renewed = Vec::new();
    for key in original_order { renewed.push(remaining.remove(&key).expect("original declaration remains")); }
    renewed.extend(remaining.into_values());
    for application in manifest["terminal_applications"].as_array_mut().unwrap() {
        let corresponding = renewed.iter().find(|binding|binding["source"] == application["source"] && binding["declaration"] == application["declaration"]).unwrap();
        application["sha256"] = corresponding["sha256"].clone();
    }
    println!("mathematical_sources={}\nmathematical_declarations={}\nretained_coherence_application_declarations={}\nretained_terminal_applications={}",sources.len(),renewed.len(),original_application["theorem_declarations"].as_array().unwrap().len(),manifest["terminal_applications"].as_array().unwrap().len());
    manifest["theorems"] = Value::Array(renewed);
    assert_eq!(manifest["assets"],original_assets); assert_eq!(manifest["coherence_application"],original_application);
    let typed: QuantumBindingManifest = serde_json::from_value(manifest).unwrap();
    let mut output = serde_json::to_vec_pretty(&typed).unwrap(); output.push(b'\n'); fs::write(path,output).unwrap();
}
