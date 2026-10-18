use serde_json::Value;
use std::{collections::BTreeSet, fs, io::Write, path::Path, process::Command};
type Checked<T> = Result<T, String>;
fn fields(value: &Value, names: &[&str]) -> Checked<()> {
    let object = value.as_object().ok_or("expected object")?;
    let actual: BTreeSet<_> = object.keys().map(String::as_str).collect();
    let expected: BTreeSet<_> = names.iter().copied().collect();
    if actual != expected { return Err("incorrect object fields".into()); }
    Ok(())
}
fn dimension(value: &Value) -> Checked<usize> {
    let size = value.as_u64().ok_or("dimension must be unsigned integer")?;
    if size > 1024 { return Err("dimension exceeds declared limit 1024".into()); }
    Ok(size as usize)
}
fn decimal(value: &Value, positive: bool) -> Checked<String> {
    let text = value.as_str().ok_or("field integers must be decimal strings")?;
    let digits = text.strip_prefix('-').unwrap_or(text);
    if digits.is_empty() || digits.len() > 4096 || !digits.bytes().all(|digit| digit.is_ascii_digit())
        || (digits.len() > 1 && digits.starts_with('0')) || text == "-0"
        || (positive && (text.starts_with('-') || text == "0")) {
        return Err("invalid canonical signed decimal or denominator".into());
    }
    Ok(text.to_owned())
}
fn integer_term(decimal: &str) -> String {
    if let Some(magnitude) = decimal.strip_prefix('-') {
        let mut predecessor = magnitude.as_bytes().to_vec();
        for digit in predecessor.iter_mut().rev() {
            if *digit > b'0' { *digit -= 1; break; }
            *digit = b'9';
        }
        let predecessor = String::from_utf8(predecessor).expect("ASCII decimal");
        let predecessor = predecessor.trim_start_matches('0');
        format!("ssrint.Negz {}", if predecessor.is_empty() { "0" } else { predecessor })
    } else { format!("ssrint.Posz {decimal}") }
}
fn scalar(value: &Value) -> Checked<String> {
    fields(value, &["numerator", "denominator"])?;
    let numerator = decimal(&value["numerator"], false)?;
    let denominator = decimal(&value["denominator"], true)?;
    Ok(format!("rat.divq (rat.ratz ({})) (rat.ratz ({}))", integer_term(&numerator), integer_term(&denominator)))
}
#[derive(Debug)]
struct MatrixInput { rows: usize, columns: usize, entries: Vec<Vec<String>> }
impl MatrixInput {
    fn read(value: &Value, rows: usize, columns: usize) -> Checked<Self> {
        fields(value, &["rows", "columns", "entries"])?;
        if dimension(&value["rows"])? != rows || dimension(&value["columns"])? != columns {
            return Err("incompatible matrix dimensions".into());
        }
        let source = value["entries"].as_array().ok_or("matrix entries must be rows")?;
        if source.len() != rows { return Err("incorrect row count".into()); }
        let entries = source.iter().map(|row| {
            let source = row.as_array().ok_or("matrix row must be an array")?;
            if source.len() != columns { return Err("ragged or incorrect column count".into()); }
            source.iter().map(scalar).collect::<Checked<Vec<_>>>()
        }).collect::<Checked<Vec<_>>>()?;
        Ok(Self { rows, columns, entries })
    }
    fn declaration(&self, name: &str) -> String {
        let list = |values: &[String]| format!("({})", values.iter().rev().fold("nil".to_owned(), |tail, item| format!("({item})::{tail}")));
        let rows = self.entries.iter().map(|row| list(row)).collect::<Vec<_>>();
        format!("Definition {name} := rational_literal_matrix {} {} {}.\n", self.rows, self.columns, list(&rows))
    }
}
fn matrix_equation_proof(rows: usize, columns: usize) -> String {
    let pattern = |size: usize, name: &str| (0..size).fold(name.to_owned(), |rest, _| format!("[|{rest}]"));
    let mut proof = String::from("apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.\n");
    if rows == 0 { proof.push_str("destruct row as [row bound]; discriminate.\n"); return proof; }
    if columns == 0 { proof.push_str("destruct column as [column bound]; discriminate.\n"); return proof; }
    proof.push_str("unfold operator, upper_left, upper_right, lower_left, lower_right, kernel, kernel_left_inverse, rational_literal_matrix, matrix_zero.\nrepeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].\n");
    proof.push_str(&format!("case: row => [{} row_bound]; case: column => [{} column_bound]; try discriminate;\n", pattern(rows,"row"),pattern(columns,"column")));
    proof.push_str("cbn [fintype.nat_of_ord List.nth]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.\n");
    proof
}

fn render(value: &Value) -> Checked<String> {
    fields(value, &["schema", "field", "rows", "columns", "rank", "operator", "upper_left", "upper_right", "lower_left", "lower_right", "kernel", "kernel_left_inverse"])?;
    if value["schema"] != "exact-rank-kernel-v1" || value["field"] != "rational" {
        return Err("unsupported schema or field encoding".into());
    }
    let rows = dimension(&value["rows"])?;
    let columns = dimension(&value["columns"])?;
    let rank = dimension(&value["rank"])?;
    if rank > rows || rank > columns { return Err("rank exceeds operator dimensions".into()); }
    let width = columns - rank;
    let specifications = [("operator",rows,columns),("upper_left",rows,rank),("upper_right",rank,columns),
        ("lower_left",rank,rows),("lower_right",columns,rank),("kernel",columns,width),("kernel_left_inverse",width,columns)];
    let mut result = String::from("(** Exact equations validate the proposed rational rank and complete kernel frame. *)\nFrom Stdlib Require Import List.\nFrom mathcomp Require boot order algebra.\nFrom OpenGororoba Require Import FiniteMatrixConventions ExactRankCertificate.\nImport ssreflect ssrbool divalg matrix mxalgebra rat.\n");
    for (name, rows, columns) in specifications {
        result.push_str(&MatrixInput::read(&value[name], rows, columns)?.declaration(name));
    }
    result.push_str("Example retained_rank_equations : rank_certificate_check rat.rat_rat__canonical__GRing_Field operator upper_left upper_right lower_left lower_right = true.\nProof. unfold rank_certificate_check. apply Bool.andb_true_iff. split.\n- ");
    result.push_str(&matrix_equation_proof(rows, columns));
    result.push_str("- "); result.push_str(&matrix_equation_proof(rank, rank)); result.push_str("Qed.\n");
    result.push_str(&format!("Theorem retained_exact_rank : mxalgebra.mxrank operator = {rank}.\nProof. exact (@rank_certificate_check_sound rat.rat_rat__canonical__GRing_Field {rows} {columns} {rank} operator upper_left upper_right lower_left lower_right retained_rank_equations). Qed.\nExample retained_kernel_equations : kernel_frame_check rat.rat_rat__canonical__GRing_Field {rank} operator kernel kernel_left_inverse = true.\nProof. unfold kernel_frame_check. apply Bool.andb_true_iff. split.\n- "));
    result.push_str(&matrix_equation_proof(rows, width));
    result.push_str("- apply Bool.andb_true_iff. split.\n  + "); result.push_str(&matrix_equation_proof(width,width));
    result.push_str("  + reflexivity.\nQed.\n");
    result.push_str("Theorem retained_kernel_spans : forall vector : matrix.matrix rat.rat ");
    result.push_str(&format!("{columns} 1, matrix.mulmx operator vector = matrix_zero _ {rows} 1 -> exists coefficients, vector = matrix.mulmx kernel coefficients.\nProof. exact (@checked_kernel_frame_complete rat.rat_rat__canonical__GRing_Field {rows} {columns} {width} {rank} operator kernel kernel_left_inverse retained_exact_rank retained_kernel_equations). Qed.\nPrint Assumptions retained_exact_rank.\nPrint Assumptions retained_kernel_spans.\n"));
    Ok(result)
}
fn run(source: &Path, destination: &Path) -> Checked<()> {
    let metadata = fs::metadata(source).map_err(|error| error.to_string())?;
    if metadata.len() > 16 * 1024 * 1024 { return Err("certificate exceeds 16 MiB".into()); }
    let bytes = fs::read(source).map_err(|error| error.to_string())?;
    let value: Value = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    let proof = render(&value)?;
    if fs::read(source).map_err(|error| error.to_string())? != bytes { return Err("source changed during ingestion".into()); }
    let mut hash = Command::new("sha256sum").stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().map_err(|error| error.to_string())?;
    hash.stdin.take().ok_or("hash input unavailable")?.write_all(&bytes).map_err(|error| error.to_string())?;
    let output = hash.wait_with_output().map_err(|error| error.to_string())?;
    if !output.status.success() { return Err("source hash failed".into()); }
    let hash = String::from_utf8(output.stdout).map_err(|error| error.to_string())?;
    let digest = hash.split_whitespace().next().ok_or("missing source hash")?;
    let mut file = fs::OpenOptions::new().write(true).create_new(true).open(destination).map_err(|error| error.to_string())?;
    file.write_all(format!("(** Input SHA-256: {digest}. *)\n{proof}").as_bytes()).map_err(|error| error.to_string())?;
    println!("proposed_source_sha256={digest}; Rocq compilation must validate every equation");
    Ok(())
}
fn main() {
    let arguments: Vec<_> = std::env::args_os().collect();
    if arguments.len() != 3 { eprintln!("usage: ingest_rank_certificate INPUT_JSON FRESH_OUTPUT_V"); std::process::exit(2); }
    if let Err(error) = run(Path::new(&arguments[1]), Path::new(&arguments[2])) { eprintln!("{error}"); std::process::exit(1); }
}
#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    #[test] fn reject_bad_scalars() {
        for (numerator, denominator) in [("01","1"),("-0","1"),("+1","1"),("1","0"),("1","-2"),("1/2","1")] {
            assert!(scalar(&json!({"numerator":numerator,"denominator":denominator})).is_err());
        }
        assert!(scalar(&json!({"numerator":1,"denominator":"1"})).is_err());
    }
    #[test] fn encode_negative_predecessor() {
        assert_eq!(integer_term("-1"),"ssrint.Negz 0");
        assert_eq!(integer_term("-1000"),"ssrint.Negz 999");
    }
    #[test] fn reject_ragged_and_incompatible_matrices() {
        assert!(MatrixInput::read(&json!({"rows":2,"columns":1,"entries":[[],[]]}),2,1).is_err());
        assert!(MatrixInput::read(&json!({"rows":1,"columns":1,"entries":[]}),2,1).is_err());
    }
    #[test] fn preserve_empty_dimensions() {
        assert!(MatrixInput::read(&json!({"rows":0,"columns":2,"entries":[]}),0,2).is_ok());
        assert!(MatrixInput::read(&json!({"rows":2,"columns":0,"entries":[[],[]]}),2,0).is_ok());
    }
    #[test] fn reject_unknown_fields_and_invalid_dimensions() {
        assert!(fields(&json!({"rows":0,"extra":0}), &["rows"]).is_err());
        assert!(dimension(&json!(1.5)).is_err()); assert!(dimension(&json!(-1)).is_err());
        assert!(dimension(&json!(1025)).is_err());
    }
}
