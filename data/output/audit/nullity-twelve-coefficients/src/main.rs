use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use serde_json::Value;
use std::{collections::BTreeMap, fs, path::Path, str::FromStr};

type Checked<T> = Result<T, String>;

struct SparseMatrix {
    entries: BTreeMap<(usize, usize), BigRational>,
}

impl SparseMatrix {
    fn parse(value: &Value, rows: usize, columns: usize) -> Checked<Self> {
        let object = value.as_object().ok_or("matrix must be an object")?;
        if object.len() != 2
            || !object.contains_key("shape")
            || !object.contains_key("nonzero_entries")
        {
            return Err("incorrect sparse matrix fields".into());
        }
        if value["shape"] != serde_json::json!([rows, columns]) {
            return Err("incompatible matrix shape".into());
        }
        let mut entries = BTreeMap::new();
        let source = value["nonzero_entries"]
            .as_array()
            .ok_or("entries must be an array")?;
        let mut previous = None;
        for entry in source {
            let triple = entry.as_array().ok_or("entry must be an array")?;
            if triple.len() != 3 {
                return Err("entry must have three fields".into());
            }
            let row = triple[0].as_u64().ok_or("row must be unsigned")? as usize;
            let column = triple[1].as_u64().ok_or("column must be unsigned")? as usize;
            if row >= rows
                || column >= columns
                || previous.is_some_and(|last| (row, column) <= last)
            {
                return Err("out-of-range, duplicate or unordered sparse entry".into());
            }
            let text = triple[2].as_str().ok_or("rational must be a string")?;
            if text.len() > 256 {
                return Err("scalar exceeds the certificate bound".into());
            }
            let parts = text.split('/').collect::<Vec<_>>();
            if parts.is_empty() || parts.len() > 2 {
                return Err("invalid rational".into());
            }
            let numerator = BigInt::from_str(parts[0]).map_err(|_| "invalid numerator")?;
            let denominator = if parts.len() == 2 {
                BigInt::from_str(parts[1]).map_err(|_| "invalid denominator")?
            } else {
                BigInt::one()
            };
            if denominator <= BigInt::zero() {
                return Err("denominator must be positive".into());
            }
            let coefficient = BigRational::new(numerator, denominator);
            if coefficient.is_zero() || coefficient.to_string() != text {
                return Err("sparse coefficient must be canonical and nonzero".into());
            }
            entries.insert((row, column), coefficient);
            previous = Some((row, column));
        }
        Ok(Self { entries })
    }

    fn entry(&self, row: usize, column: usize) -> BigRational {
        self.entries
            .get(&(row, column))
            .cloned()
            .unwrap_or_default()
    }

    fn declaration(&self, name: &str) -> Checked<String> {
        let mut terms = Vec::new();
        for (&(row, column), coefficient) in &self.entries {
            if !coefficient.is_integer() {
                return Err("coefficient table must be integral".into());
            }
            terms.push(format!(
                "({row}%nat,{column}%nat,({})%Z)",
                coefficient.to_integer()
            ));
        }
        Ok(format!(
            "Definition {name} : list (nat * nat * Z) := [{}].\n",
            terms.join(";")
        ))
    }
}

struct Certificate {
    coefficients: SparseMatrix,
    generators: SparseMatrix,
    reconstruction: SparseMatrix,
    monomials: Vec<(usize, usize)>,
}

fn validate(value: &Value) -> Checked<Certificate> {
    let locus = &value["quadratic_locus"];
    let coefficients = SparseMatrix::parse(&locus["coefficient_matrix"], 58, 231)?;
    let generators = SparseMatrix::parse(&locus["rref_generator_coefficients"], 8, 231)?;
    let reconstruction = SparseMatrix::parse(&locus["rref_generator_reconstruction"], 58, 8)?;
    let monomials = (0..21)
        .map(|index| (index, index))
        .chain((0..21).flat_map(|left| (left + 1..21).map(move |right| (left, right))))
        .collect::<Vec<_>>();
    if locus["monomial_pairs"] != serde_json::json!(monomials) {
        return Err("incorrect square-first lexicographic monomial order".into());
    }
    for row in 0..58 {
        for column in 0..231 {
            let product: BigRational = (0..8)
                .map(|inner| reconstruction.entry(row, inner) * generators.entry(inner, column))
                .sum();
            if product != coefficients.entry(row, column) {
                return Err(format!(
                    "coefficient reconstruction fails at ({row},{column})"
                ));
            }
        }
    }
    let pivots = [6, 111, 121, 122, 123, 124, 125, 135];
    if locus["rank_minor_columns"] != serde_json::json!(pivots) {
        return Err("incorrect generator pivot columns".into());
    }
    for row in 0..8 {
        for (column, &pivot) in pivots.iter().enumerate() {
            let expected = if row == column {
                BigRational::one()
            } else {
                BigRational::zero()
            };
            if generators.entry(row, pivot) != expected {
                return Err("generator pivot identity fails".into());
            }
        }
    }
    Ok(Certificate {
        coefficients,
        generators,
        reconstruction,
        monomials,
    })
}

fn render(certificate: &Certificate) -> Checked<String> {
    let mut output = String::from(
        "(** Complete retained coefficient equations, independent of curve realization. *)\nFrom Stdlib Require Import Reals Lra Lia List ZArith.\nFrom OpenGororoba Require Import NullityTwelveQuadraticLocus.\nImport ListNotations.\nOpen Scope R_scope.\n",
    );
    for (name, matrix) in [
        ("selected_coefficients", &certificate.coefficients),
        ("selected_reduced_coefficients", &certificate.generators),
        (
            "selected_reconstruction_coefficients",
            &certificate.reconstruction,
        ),
    ] {
        output.push_str(&matrix.declaration(name)?);
    }
    output.push_str("Definition selected_monomials : list (nat * nat) := [");
    output.push_str(
        &certificate
            .monomials
            .iter()
            .map(|(left, right)| format!("({left}%nat,{right}%nat)"))
            .collect::<Vec<_>>()
            .join(";"),
    );
    output.push_str("].\n");
    output.push_str(
        r#"
Definition sparse_integer_entry (entries : list (nat * nat * Z)) (row column : nat) : Z :=
  fold_right (fun entry total => let '(entry_row,entry_column,coefficient) := entry in
    if andb (Nat.eqb entry_row row) (Nat.eqb entry_column column)
    then (coefficient + total)%Z else total) 0%Z entries.
Definition canonical_selected_monomials : list (nat * nat) :=
  map (fun index => (index,index)) (seq 0 21) ++
  flat_map (fun monomial_left => map (fun monomial_right => (monomial_left,monomial_right))
    (seq (S monomial_left) (Nat.sub 20 monomial_left))) (seq 0 21).
Theorem selected_monomial_order : selected_monomials = canonical_selected_monomials.
Proof. vm_compute. reflexivity. Qed.
Definition selected_complete_reconstruction_check : bool :=
  forallb (fun row => forallb (fun column =>
    Z.eqb (sparse_integer_entry selected_coefficients row column)
      (fold_right (fun inner total =>
        (sparse_integer_entry selected_reconstruction_coefficients row inner *
         sparse_integer_entry selected_reduced_coefficients inner column + total)%Z)
        0%Z (seq 0 8))) (seq 0 231)) (seq 0 58).
Theorem selected_complete_coefficient_reconstruction :
  selected_complete_reconstruction_check = true.
Proof. vm_compute. reflexivity. Qed.
Definition selected_projected_row (row : nat) (z : nat -> R) : R :=
  fold_right (fun entry total => let '(entry_row,column,coefficient) := entry in
    if Nat.eqb entry_row row then
      let '(monomial_left,monomial_right) := nth column selected_monomials (0%nat,0%nat) in
      IZR coefficient * z monomial_left * z monomial_right + total else total) 0 selected_coefficients.
Definition selected_generator (index : nat) (z : nat -> R) : R :=
  match index with
  | 0%nat => (z 6)^2-(z 16)^2
  | 1%nat => z 5*z 6-z 13*z 16
  | 2%nat => z 13*z 6+z 16*z 5
  | 3%nat => z 17*z 5-z 13*z 20+z 16*z 17+z 20*z 6
  | 4%nat => z 13*z 19+z 18*z 5+z 16*z 18-z 19*z 6
  | 5%nat => z 19*z 5-z 13*z 18+z 16*z 19+z 18*z 6
  | 6%nat => z 13*z 17+z 20*z 5+z 16*z 20-z 17*z 6
  | 7%nat => z 16*z 6
  | _ => 0
  end.
Definition selected_reconstruction_row (row : nat) (z : nat -> R) : R :=
  match row with
"#,
    );
    for row in 0..58 {
        let terms = certificate
            .reconstruction
            .entries
            .iter()
            .filter(|&(&(entry_row, _), _)| entry_row == row)
            .map(|(&(.., column), coefficient)| {
                format!(
                    "({}) * selected_generator {column} z",
                    coefficient.to_integer()
                )
            })
            .collect::<Vec<_>>();
        if !terms.is_empty() {
            output.push_str(&format!("  | {row}%nat => {}\n", terms.join(" + ")));
        }
    }
    output.push_str("  | _ => 0\n  end.\nTheorem selected_projected_reconstruction : forall row z,\n  selected_projected_row row z = selected_reconstruction_row row z.\nProof.\n  intros row z. destruct row as ");
    output.push_str(&(0..58).fold("row".to_owned(), |tail, _| format!("[|{tail}]")));
    output.push_str(";\n    cbn [selected_projected_row selected_coefficients selected_monomials\n      selected_reconstruction_row selected_generator List.fold_right List.nth Nat.eqb IZR]; ring.\nQed.\n");
    output.push_str(
        r#"
Theorem selected_generators_recovered : forall z,
  selected_generator 0 z = selected_projected_row 30 z / 2 + selected_projected_row 52 z / 4 /\
  selected_generator 1 z = selected_projected_row 53 z / 4 /\
  selected_generator 2 z = - selected_projected_row 52 z / 4 /\
  selected_generator 3 z = - selected_projected_row 35 z / 2 /\
  selected_generator 4 z = - selected_projected_row 36 z / 2 /\
  selected_generator 5 z = selected_projected_row 33 z / 2 /\
  selected_generator 6 z = selected_projected_row 34 z / 2 /\
  selected_generator 7 z = selected_projected_row 31 z / 4 + selected_projected_row 53 z / 8.
Proof.
  intro z. repeat rewrite selected_projected_reconstruction.
  cbn [selected_reconstruction_row selected_generator]. repeat split; field.
Qed.
Theorem selected_projected_zero_iff_generators : forall z,
  (forall row, (row < 58)%nat -> selected_projected_row row z = 0) <->
  quadratic_common_zero (z 5) (z 6) (z 13) (z 16) (z 17) (z 18) (z 19) (z 20).
Proof.
  intro z; split.
  - intro projected_zero.
    pose proof (selected_generators_recovered z) as recovered.
    assert (p30 := projected_zero 30 ltac:(lia)).
    assert (p31 := projected_zero 31 ltac:(lia)).
    assert (p33 := projected_zero 33 ltac:(lia)).
    assert (p34 := projected_zero 34 ltac:(lia)).
    assert (p35 := projected_zero 35 ltac:(lia)).
    assert (p36 := projected_zero 36 ltac:(lia)).
    assert (p52 := projected_zero 52 ltac:(lia)).
    assert (p53 := projected_zero 53 ltac:(lia)).
    rewrite p30,p31,p33,p34,p35,p36,p52,p53 in recovered.
    cbn [selected_generator] in recovered.
    unfold quadratic_common_zero; destruct recovered as [? [? [? [? [? [? [? ?]]]]]]];
      repeat split; lra.
  - intro common_zero. unfold quadratic_common_zero in common_zero.
    destruct common_zero as [g0 [g1 [g2 [g3 [g4 [g5 [g6 g7]]]]]]].
    assert (generator_zero : forall index, selected_generator index z = 0).
    { intro index. destruct index as [|[|[|[|[|[|[|[|index]]]]]]]];
        cbn [selected_generator]; assumption || reflexivity. }
    intros row bound. rewrite selected_projected_reconstruction.
"#,
    );
    output.push_str("    destruct row as ");
    output.push_str(&(0..58).fold("row".to_owned(), |tail, _| format!("[|{tail}]")));
    output.push_str(
        "; cbn [selected_reconstruction_row]; repeat rewrite generator_zero; ring.\nQed.\n",
    );
    output.push_str(
        r#"
Theorem selected_projected_real_zero_set : forall z,
  (forall row, (row < 58)%nat -> selected_projected_row row z = 0) <->
  coordinate_plane_a15 (z 6) (z 16) (z 17) (z 18) (z 19) (z 20) \/
  coordinate_plane_b17 (z 5) (z 6) (z 13) (z 16).
Proof.
  intro z. rewrite selected_projected_zero_iff_generators.
  apply selected_quadratic_zero_set.
Qed.
Print Assumptions selected_complete_coefficient_reconstruction.
Print Assumptions selected_monomial_order.
Print Assumptions selected_projected_reconstruction.
Print Assumptions selected_projected_real_zero_set.
"#,
    );
    for prefix in [
        "z ",
        "selected_generator ",
        "selected_projected_row ",
        "projected_zero ",
    ] {
        let mut scoped = String::new();
        let mut remaining = output.as_str();
        while let Some(position) = remaining.find(prefix) {
            scoped.push_str(&remaining[..position + prefix.len()]);
            remaining = &remaining[position + prefix.len()..];
            let digits = remaining.bytes().take_while(u8::is_ascii_digit).count();
            scoped.push_str(&remaining[..digits]);
            if digits > 0 && !remaining[digits..].starts_with("%nat") {
                scoped.push_str("%nat");
            }
            remaining = &remaining[digits..];
        }
        scoped.push_str(remaining);
        output = scoped;
    }
    Ok(output)
}

fn run(source: &Path, destination: &Path) -> Checked<()> {
    let bytes = fs::read(source).map_err(|error| error.to_string())?;
    if bytes.len() > 16 * 1024 * 1024 {
        return Err("input exceeds 16 MiB".into());
    }
    let value: Value = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    let certificate = validate(&value)?;
    let proof = render(&certificate)?;
    if fs::read(source).map_err(|error| error.to_string())? != bytes {
        return Err("source changed during ingestion".into());
    }
    fs::write(destination, proof).map_err(|error| error.to_string())?;
    println!("validated_rows=58 monomials=231 generators=8; Rocq must check the emitted equations");
    Ok(())
}

fn main() {
    let arguments = std::env::args_os().collect::<Vec<_>>();
    if arguments.len() != 3 {
        eprintln!("usage: nullity-coefficient-certificate INPUT_JSON OUTPUT_V");
        std::process::exit(2);
    }
    if let Err(error) = run(Path::new(&arguments[1]), Path::new(&arguments[2])) {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn sparse_matrices_reject_collisions_and_bad_shape() {
        for input in [
            json!({"shape":[2,2],"nonzero_entries":[[0,0,"1"],[0,0,"2"]]}),
            json!({"shape":[2,2],"nonzero_entries":[[2,0,"1"]]}),
            json!({"shape":[1,2],"nonzero_entries":[]}),
            json!({"shape":[2,2],"nonzero_entries":[[0,0,"0"]]}),
            json!({"shape":[2,2],"nonzero_entries":[[0,0,"1/0"]]}),
            json!({"shape":[2,2],"nonzero_entries":[[0,0,"2/2"]]}),
        ] {
            assert!(SparseMatrix::parse(&input, 2, 2).is_err());
        }
    }

    #[test]
    fn sparse_matrix_preserves_signed_fractions_and_zero_fill() {
        let matrix = SparseMatrix::parse(
            &json!({"shape":[2,2],"nonzero_entries":[[0,1,"-3/2"]]}),
            2,
            2,
        )
        .unwrap();
        assert_eq!(matrix.entry(0, 1).to_string(), "-3/2");
        assert_eq!(matrix.entry(1, 0).to_string(), "0");
    }

    #[test]
    fn retained_reconstruction_and_coordinate_mutations() {
        let path = std::env::var("NULLITY_SOURCE").unwrap();
        let source: serde_json::Value =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        assert!(validate(&source).is_ok());
        let mut corrupted = source.clone();
        corrupted["quadratic_locus"]["coefficient_matrix"]["nonzero_entries"][0][2] = json!("3");
        assert!(validate(&corrupted).is_err());
        let mut omitted = source.clone();
        omitted["quadratic_locus"]["coefficient_matrix"]["nonzero_entries"]
            .as_array_mut()
            .unwrap()
            .pop();
        assert!(validate(&omitted).is_err());
        let mut wrong_order = source;
        wrong_order["quadratic_locus"]["monomial_pairs"]
            .as_array_mut()
            .unwrap()
            .swap(0, 1);
        assert!(validate(&wrong_order).is_err());
    }
}
