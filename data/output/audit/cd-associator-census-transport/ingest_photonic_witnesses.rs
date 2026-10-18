use serde_json::Value;
use std::{collections::BTreeSet, fs, path::Path, process::Command};
fn integer(value: &Value) -> i64 { value.as_i64().expect("integer certificate field") }
fn sign(value: &Value) -> i64 { let result = integer(value); assert!([-1,1].contains(&result)); result }
fn digest(path: &Path) -> String {
    let output = Command::new("sha256sum").arg(path).output().unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout).unwrap().split_whitespace().next().unwrap().to_owned()
}
fn checked_digest(path: &Path, bytes: &[u8]) -> String {
    use std::io::Write;
    let mut child = Command::new("sha256sum").stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(bytes).unwrap();
    let result = child.wait_with_output().unwrap();
    assert!(result.status.success());
    let identity = String::from_utf8(result.stdout).unwrap().split_whitespace().next().unwrap().to_owned();
    assert_eq!(digest(path), identity, "source identity changed after read");
    assert_eq!(fs::read(path).unwrap(), bytes, "source bytes changed after read");
    identity
}
fn main() {
    let arguments: Vec<_> = std::env::args().collect();
    assert_eq!(arguments.len(), 3, "usage: ingest IBMQUANTUM OUTPUT");
    let source = Path::new(&arguments[1]);
    let output = Path::new(&arguments[2]);
    fs::create_dir(output).unwrap();
    let census_path = source.join("docs/evidence/box_kite_census/census.json");
    let census_bytes = fs::read(&census_path).unwrap();
    let census: Value = serde_json::from_slice(&census_bytes).unwrap();
    assert_eq!(census["schema"], "box-kite-census-v1");
    let columns = census["design_b"]["columns"].as_array().unwrap();
    let column = |name: &str| columns.iter().position(|value| value == name).expect("census column");
    let mut configurations = BTreeSet::new();
    let mut identifiers = BTreeSet::new();
    let mut evidence = format!("{}  docs/evidence/box_kite_census/census.json\n", checked_digest(&census_path, &census_bytes));
    fs::write(output.join("census.json"), census_bytes).unwrap();
    let mut declarations = String::from("(** Retained photonic sign blocks; Rocq checks every witness equation. *)\nFrom Stdlib Require Import List ZArith.\nFrom OpenGororoba Require Import M3IsAssociator CDSignNumericCorrespondence CDAssociatorDoubling.\nImport ListNotations.\nLocal Open Scope Z_scope.\nDefinition photonic_witness_block (w : nat * nat * Z * nat * nat * Z) : list Z :=\n  let '(i,j,s,k,l,_) := w in\n  [M3IsAssociator.cd_sign_fuel 4 16 i k; s * M3IsAssociator.cd_sign_fuel 4 16 j l;\n   s * M3IsAssociator.cd_sign_fuel 4 16 j k; M3IsAssociator.cd_sign_fuel 4 16 i l].\n");
    let mut coverage = String::from("config\tmanifest\trow_count\tinput_offset\toutput_label_modes\twitness\n");
    let mut witnesses = Vec::new();
    let case_root = source.join("results/quandela/cases/box_kite_photonic_single");
    let mut paths: Vec<_> = fs::read_dir(&case_root).unwrap().map(|entry| entry.unwrap().path().join("cases.json")).filter(|path| path.is_file()).collect();
    paths.sort();
    for path in paths {
        let bytes = fs::read(&path).unwrap();
        let manifest: Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(manifest["schema"], "qd-box-kite-cases-v1");
        let blocks = manifest["blocks"].as_array().unwrap();
        for block in blocks.iter().filter(|block| block["kind"] == "two_label") {
            let name = block["config"].as_str().unwrap();
            assert!(identifiers.insert(name.to_owned()), "duplicate physical configuration");
            let rows = block["m"].as_array().unwrap(); assert_eq!(rows.len(),2);
            let mut matrix = Vec::new();
            for row in rows { let entries = row.as_array().unwrap(); assert_eq!(entries.len(),2); matrix.extend(entries.iter().map(sign)); }
            let partner_sign = sign(&block["t"]);
            let key = (matrix.clone(), partner_sign);
            assert!(configurations.insert(key), "duplicate matrix/sign configuration");
            let labels = block["roles"].as_array().unwrap();
            assert_eq!(labels.len(),4); assert_eq!(labels[0],"label_0"); assert_eq!(labels[1],"label_1");
            let offset = integer(&block["offset"]); assert_eq!(block["photons"],serde_json::json!([offset]));
            let row_refs = block["rows"].as_array().unwrap();
            let witness = if let Some(explicit) = block.get("witness") {
                let fields = explicit.as_array().unwrap(); assert_eq!(fields.len(),6); fields.iter().map(integer).collect::<Vec<_>>()
            } else {
                let first = row_refs.first().expect("configuration needs witness or census row").as_array().unwrap();
                assert_eq!(first.len(),2);
                let family = first[0].as_str().unwrap(); assert!(["within_kite","nonkite_pairs"].contains(&family));
                let index = first[1].as_u64().unwrap() as usize;
                let row = census["design_b"][family][index].as_array().unwrap();
                ["p_low","p_high","x_sign","q_low","q_high","y_sign"].iter().map(|name| integer(&row[column(name)])).collect()
            };
            assert!(witness.iter().enumerate().all(|(index,value)| if [2,5].contains(&index) { [-1,1].contains(value) } else { (1..16).contains(value) }));
            assert_eq!(witness[5],partner_sign);
            assert_eq!(witness[0]^witness[1],witness[3]^witness[4]);
            let list = matrix.iter().map(ToString::to_string).collect::<Vec<_>>().join("; ");
            let tuple = format!("({}%nat,{}%nat,{},{}%nat,{}%nat,{})",witness[0],witness[1],witness[2],witness[3],witness[4],witness[5]);
            let index = witnesses.len();
            declarations.push_str(&format!("Definition retained_sparse_witness_{index} := {tuple}.\nExample retained_sparse_block_{index} : photonic_witness_block retained_sparse_witness_{index} = [{list}].\nProof. vm_compute. reflexivity. Qed.\n"));
            witnesses.push((tuple,matrix,partner_sign));
            let relative = path.strip_prefix(source).unwrap();
            evidence.push_str(&format!("{}  {}\n",checked_digest(&path, &bytes),relative.display()));
            let filename = format!("{name}.cases.json"); fs::write(output.join(filename),&bytes).unwrap();
            coverage.push_str(&format!("{name}\t{}\t{}\t{offset}\t{},{}\t{witness:?}\n",relative.display(),row_refs.len(),offset,offset+1));
        }
    }
    assert_eq!(configurations.len(),32,"complete 16-matrix/two-sign family");
    for first in [-1,1] { for second in [-1,1] { for third in [-1,1] { for fourth in [-1,1] { for partner in [-1,1] {
        assert!(configurations.contains(&(vec![first,second,third,fourth],partner)), "missing configuration");
    }}}}}
    fs::write(output.join("source-identities.sha256"), evidence).unwrap();
    fs::write(output.join("configuration-coverage.tsv"), coverage).unwrap();
    declarations.push_str("Definition retained_sparse_configurations : list (list Z * Z) := [\n");
    declarations.push_str(&witnesses.iter().map(|(_,matrix,partner)| format!("([{}],{})",matrix.iter().map(ToString::to_string).collect::<Vec<_>>().join("; "),partner)).collect::<Vec<_>>().join(";\n"));
    declarations.push_str("\n].\nTheorem retained_sparse_configuration_coverage : forall first second third fourth partner : bool,\n  In ([phase_sign first; phase_sign second; phase_sign third; phase_sign fourth], phase_sign partner) retained_sparse_configurations.\nProof. intros [] [] [] [] []; vm_compute; tauto. Qed.\nPrint Assumptions retained_sparse_configuration_coverage.\n");
    declarations.push_str("Definition retained_sparse_witnesses : list (nat * nat * Z * nat * nat * Z) := [\n");
    declarations.push_str(&witnesses.iter().map(|(tuple,_,_)| tuple.as_str()).collect::<Vec<_>>().join(";\n"));
    declarations.push_str("\n].\nDefinition photonic_witness_configuration (w : nat * nat * Z * nat * nat * Z) :=\n  let '(_,_,_,_,_,t) := w in (photonic_witness_block w,t).\nTheorem retained_sparse_witness_map : map photonic_witness_configuration retained_sparse_witnesses = retained_sparse_configurations.\nProof. vm_compute. reflexivity. Qed.\nTheorem retained_sparse_witness_total : forall configuration, In configuration retained_sparse_configurations ->\n  exists witness, In witness retained_sparse_witnesses /\\ photonic_witness_configuration witness = configuration.\nProof. intros configuration member. rewrite <- retained_sparse_witness_map in member.\n  apply in_map_iff in member. destruct member as [witness [equation member]]. exists witness. auto. Qed.\nPrint Assumptions retained_sparse_witness_map.\nPrint Assumptions retained_sparse_witness_total.\n");
    declarations.push_str("Definition photonic_witness_domain (w : nat * nat * Z * nat * nat * Z) : bool :=\n  let '(i,j,s,k,l,t) := w in\n  andb (andb (andb (Nat.ltb 0 i) (Nat.ltb i 16)) (andb (Nat.ltb 0 j) (Nat.ltb j 16)))\n    (andb (andb (andb (Nat.ltb 0 k) (Nat.ltb k 16)) (andb (Nat.ltb 0 l) (Nat.ltb l 16)))\n      (andb (andb (negb (Nat.eqb i j)) (negb (Nat.eqb k l)))\n        (andb (Nat.eqb (Nat.lxor i j) (Nat.lxor k l))\n          (andb (orb (Z.eqb s 1) (Z.eqb s (-1))) (orb (Z.eqb t 1) (Z.eqb t (-1))))))).\nTheorem retained_sparse_witness_domains : Forall (fun witness => photonic_witness_domain witness = true) retained_sparse_witnesses.\nProof. vm_compute. repeat constructor. Qed.\nPrint Assumptions retained_sparse_witness_domains.\n");
    fs::write(output.join("SparsePhotonicCertificates.v"),declarations).unwrap();
    println!("retained_configurations={}\nretained_witnesses={}\nindependent_measurement_count=requires_physical_application_contract", configurations.len(),witnesses.len());
}
