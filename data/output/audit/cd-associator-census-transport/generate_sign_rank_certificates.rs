use std::fs;
fn integer(value:i64)->String { if value>=0 {format!("(rat.ratz (ssrint.Posz {value}))")} else {format!("(rat.ratz (ssrint.Negz {}))",-value-1)} }
fn rational(numerator:i64,denominator:i64)->String { if denominator==1 {integer(numerator)} else {format!("(rat.divq {} {})",integer(numerator),integer(denominator))} }
fn matrix(rows:&[Vec<(i64,i64)>])->String { format!("(rational_literal_matrix {} {} ({}::nil))",rows.len(),rows[0].len(),rows.iter().map(|row|format!("({}::nil)",row.iter().map(|&(a,b)|rational(a,b)).collect::<Vec<_>>().join("::"))).collect::<Vec<_>>().join("::")) }
fn main(){
 let path="proofs/theories/RationalSignBlockRanks.v";
 let mut output=String::from("(** Exact upper and lower certificates for every two-label sign matrix. *)\nFrom Stdlib Require Import Arith List.\nFrom mathcomp Require boot order algebra.\nFrom OpenGororoba Require Import FiniteMatrixConventions.\nImport ssreflect divalg matrix mxalgebra rat.\n");
 for bits in 0..16 {
  let signs:Vec<_>=(0..4).map(|index|if bits&(1<<index)==0 {1i64}else{-1i64}).collect();
  let a=signs[0];let b=signs[1];let c=signs[2];let d=signs[3];let det=a*d-b*c; let rank=if det==0{1}else{2};
  let bools=(0..4).map(|index|if bits&(1<<index)==0{"false"}else{"true"}).collect::<Vec<_>>().join(" ");
  let op=format!("(rational_sign_block {bools})");
  let (upper_left,upper_right,lower_left,lower_right)=if rank==1 {
    (matrix(&[vec![(a,1)],vec![(c,1)]]),matrix(&[vec![(1,1),(a*b,1)]]),matrix(&[vec![(a,1),(0,1)]]),matrix(&[vec![(1,1)],vec![(0,1)]]))
  }else{
    let sign=det/2; let identity=matrix(&[vec![(1,1),(0,1)],vec![(0,1),(1,1)]]);
    (op.clone(),identity.clone(),matrix(&[vec![(sign*d,2),(-sign*b,2)],vec![(-sign*c,2),(sign*a,2)]]),identity)
  };
  output.push_str(&format!("Lemma rational_sign_rank_{bits} : mxalgebra.mxrank {op} = {rank}.\nProof.\n  apply (@matrix_rank_witness_sound _ 2 2 {rank} {op} {upper_left} {upper_right} {lower_left} {lower_right}).\n"));
  for _ in 0..2 {
   output.push_str("  - apply (proj1 (matrix.matrixP _ _)). intros row column.\n    unfold rational_sign_block, rational_literal_matrix.\n    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].\n    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;\n    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.\n");
  }
  output.push_str("Qed.\n");
 }
 output.push_str("Theorem rational_sign_block_rank : forall first second third fourth,\n  mxalgebra.mxrank (rational_sign_block first second third fourth) =\n  if xorb (xorb first second) (xorb third fourth) then 2 else 1.\nProof. intros [] [] [] []; first [apply rational_sign_rank_0 | apply rational_sign_rank_1 | apply rational_sign_rank_2 | apply rational_sign_rank_3 | apply rational_sign_rank_4 | apply rational_sign_rank_5 | apply rational_sign_rank_6 | apply rational_sign_rank_7 | apply rational_sign_rank_8 | apply rational_sign_rank_9 | apply rational_sign_rank_10 | apply rational_sign_rank_11 | apply rational_sign_rank_12 | apply rational_sign_rank_13 | apply rational_sign_rank_14 | apply rational_sign_rank_15]. Qed.\nPrint Assumptions matrix_rank_witness_sound.\nPrint Assumptions rational_sign_block_rank.\n");
 fs::write(path,output.replacen("Require Import Arith.","Require Import Arith List.",1)).unwrap();
}
