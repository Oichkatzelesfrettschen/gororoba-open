(** Natural-index data checks reflect exact equations into MathComp matrices. *)
From Stdlib Require Import List Arith Lia Bool.
From mathcomp Require boot order algebra.
Import ssreflect ssrbool matrix rat fintype.
Import -(coercions) rings_modules_and_algebras divalg.
Import divalg.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition rational_data_matrix rows columns (entry : nat -> nat -> rat.rat) :=
  @matrix.matrix_of_fun rat.rat rows columns matrix.matrix_key
    (fun row column => entry (fintype.nat_of_ord row) (fintype.nat_of_ord column)).

Definition rational_data_sum count (entry : nat -> rat.rat) : rat.rat :=
  List.fold_right (fun index total => entry index + total) 0 (List.seq 0 count).

Lemma stdlib_sequence_iota start count : List.seq start count = seq.iota start count.
Proof.
  revert start; induction count as [|count induction_equal]; intro start.
  - reflexivity.
  - cbn [List.seq seq.iota]. rw induction_equal. reflexivity.
Qed.

Lemma rational_fold_big (indices : list nat) (entry : nat -> rat.rat) :
  List.fold_right (fun index total => entry index + total) 0 indices =
  \sum_(index <- indices) entry index.
Proof.
  induction indices as [|index indices induction_equal].
  - symmetry; apply bigop.big_nil.
  - cbn [List.fold_right]. rw bigop.big_cons induction_equal. reflexivity.
Qed.

Lemma rational_sum_ordinal count (entry : nat -> rat.rat) :
  rational_data_sum count entry = \sum_(index < count) entry (fintype.nat_of_ord index).
Proof.
  unfold rational_data_sum. rw rational_fold_big stdlib_sequence_iota.
  pose proof (@bigop.big_mkord rat.rat rat.zeroq rat.addq count
    (fun _ => true) entry) as ordinal_bridge.
  unfold bigop.index_iota in ordinal_bridge. rw ssrnat.subn0 in ordinal_bridge.
  exact ordinal_bridge.
Qed.

Definition rational_data_product inner
  (first second : nat -> nat -> rat.rat) row column : rat.rat :=
  rational_data_sum inner (fun index => first row index * second index column).

Theorem rational_data_product_matrix rows inner columns first second :
  matrix.mulmx (rational_data_matrix rows inner first)
    (rational_data_matrix inner columns second) =
  rational_data_matrix rows columns (rational_data_product inner first second).
Proof.
  apply (proj1 (matrix.matrixP _ _)); intros row column.
  unfold rational_data_matrix. rw !matrix.mxE.
  unfold rational_data_product. rw rational_sum_ordinal.
  apply bigop.eq_bigr; intros index _; rw !matrix.mxE. reflexivity.
Qed.

Definition rational_data_equation_check rows columns
  (first second : nat -> nat -> rat.rat) : bool :=
  List.forallb (fun row => List.forallb
    (fun column => eqtype.eq_op (first row column) (second row column))
    (List.seq 0 columns)) (List.seq 0 rows).

Theorem rational_data_equation_sound rows columns first second :
  rational_data_equation_check rows columns first second = true ->
  rational_data_matrix rows columns first = rational_data_matrix rows columns second.
Proof.
  intro accepted. apply (proj1 (matrix.matrixP _ _)); intros row column.
  unfold rational_data_matrix; rw !matrix.mxE.
  unfold rational_data_equation_check in accepted.
  pose proof (proj1 (@List.forallb_forall nat
    (fun row => List.forallb (fun column => eqtype.eq_op (first row column) (second row column))
      (List.seq 0 columns)) (List.seq 0 rows)) accepted) as accepted_rows.
  assert (row_present : List.In (fintype.nat_of_ord row) (List.seq 0 rows)).
  { apply List.in_seq. pose proof (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord row)); lia. }
  specialize (accepted_rows _ row_present).
  pose proof (proj1 (@List.forallb_forall nat
    (fun column => eqtype.eq_op (first (fintype.nat_of_ord row) column)
      (second (fintype.nat_of_ord row) column)) (List.seq 0 columns)) accepted_rows)
    as accepted_columns.
  assert (column_present : List.In (fintype.nat_of_ord column) (List.seq 0 columns)).
  { apply List.in_seq. pose proof (ssrbool.elimT ssrnat.ltP (fintype.ltn_ord column)); lia. }
  specialize (accepted_columns _ column_present).
  exact (ssrbool.elimT eqtype.eqP accepted_columns).
Qed.

Theorem rational_data_product_sound rows inner columns first second expected :
  rational_data_equation_check rows columns
    (rational_data_product inner first second) expected = true ->
  matrix.mulmx (rational_data_matrix rows inner first)
    (rational_data_matrix inner columns second) = rational_data_matrix rows columns expected.
Proof.
  intro accepted. rw rational_data_product_matrix.
  apply rational_data_equation_sound; exact accepted.
Qed.

Print Assumptions rational_data_equation_sound.
Print Assumptions rational_data_product_sound.

Definition rational_data_identity (row column : nat) : rat.rat :=
  if Nat.eqb row column then 1 else 0.
Definition rational_data_zero (_ _ : nat) : rat.rat := 0.

Theorem rational_data_identity_matrix dimension :
  rational_data_matrix dimension dimension rational_data_identity =
  matrix.scalar_mx (1 : rat.rat).
Proof.
  apply (proj1 (matrix.matrixP _ _)); intros row column.
  unfold rational_data_matrix, rational_data_identity. rw !matrix.mxE.
  case: eqtype.eqP => [equal | unequal].
  - subst column. rw Nat.eqb_refl. reflexivity.
  - assert (values_unequal : fintype.nat_of_ord row <> fintype.nat_of_ord column).
    { intro values_equal. apply unequal. apply eqtype.val_inj. exact values_equal. }
    apply Nat.eqb_neq in values_unequal. rw values_unequal. reflexivity.
Qed.

Theorem rational_data_zero_matrix rows columns :
  rational_data_matrix rows columns rational_data_zero =
  (0 : matrix.matrix rat.rat rows columns).
Proof.
  apply (proj1 (matrix.matrixP _ _)); intros row column.
  unfold rational_data_matrix, rational_data_zero. rw !matrix.mxE. reflexivity.
Qed.

Theorem rational_data_transpose_matrix rows columns entry :
  rational_data_matrix columns rows (fun row column => entry column row) =
  matrix.trmx (rational_data_matrix rows columns entry).
Proof.
  apply (proj1 (matrix.matrixP _ _)); intros row column.
  unfold rational_data_matrix. rw !matrix.mxE. reflexivity.
Qed.

Definition rational_sparse_data_product inner
  (first second : nat -> nat -> rat.rat) row column : rat.rat :=
  List.fold_right (fun index total =>
    let first_value := first row index in
    if eqtype.eq_op first_value 0 then total else
    let second_value := second index column in
    if eqtype.eq_op second_value 0 then total else first_value * second_value + total)
    0 (List.seq 0 inner).

Lemma rational_sparse_fold_equal (indices : list nat) (first second : nat -> rat.rat) :
  List.fold_right (fun index total =>
    let first_value := first index in
    if eqtype.eq_op first_value 0 then total else
    let second_value := second index in
    if eqtype.eq_op second_value 0 then total else first_value * second_value + total) 0 indices =
  List.fold_right (fun index total => first index * second index + total) 0 indices.
Proof.
  induction indices as [|index indices induction_equal]; [reflexivity|].
  cbn [List.fold_right]. rw induction_equal.
  case: eqtype.eqP => [first_zero | first_nonzero].
  - rw first_zero mul0r add0r. reflexivity.
  - case: eqtype.eqP => [second_zero | second_nonzero].
    + rw second_zero mulr0 add0r. reflexivity.
    + reflexivity.
Qed.

Theorem rational_sparse_product_equal inner first second row column :
  rational_sparse_data_product inner first second row column =
  rational_data_product inner first second row column.
Proof.
  unfold rational_sparse_data_product, rational_data_product, rational_data_sum.
  apply rational_sparse_fold_equal.
Qed.

Theorem rational_sparse_product_matrix rows inner columns first second :
  matrix.mulmx (rational_data_matrix rows inner first)
    (rational_data_matrix inner columns second) =
  rational_data_matrix rows columns (rational_sparse_data_product inner first second).
Proof.
  rw rational_data_product_matrix.
  apply (proj1 (matrix.matrixP _ _)); intros row column.
  unfold rational_data_matrix. rw !matrix.mxE rational_sparse_product_equal. reflexivity.
Qed.

Theorem rational_sparse_product_sound rows inner columns first second expected :
  rational_data_equation_check rows columns
    (rational_sparse_data_product inner first second) expected = true ->
  matrix.mulmx (rational_data_matrix rows inner first)
    (rational_data_matrix inner columns second) = rational_data_matrix rows columns expected.
Proof.
  intro accepted. rw rational_sparse_product_matrix.
  apply rational_data_equation_sound; exact accepted.
Qed.
Print Assumptions rational_sparse_product_equal.
Print Assumptions rational_sparse_product_sound.
