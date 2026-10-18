(** Recursive low/high pairs encode as column vectors with the high half last. *)
From Stdlib Require Import Reals Arith Lia.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import StdlibRealFieldAdapter RecursiveCDTower.
Import ssreflect ssrbool divalg matrix.
Fixpoint tower_dimension (order : nat) : nat :=
 match order with O => 1 | S lower => ssrnat.addn (tower_dimension lower) (tower_dimension lower) end.
(** Column counts agree with numeric sign power-of-two dimensions. *)
Theorem tower_dimension_power order : tower_dimension order = Nat.pow 2 order.
Proof.
 induction order as [|order induction_equal].
 - reflexivity.
 - change (tower_dimension order + tower_dimension order = Nat.pow 2 (S order))%nat.
   rw induction_equal. simpl. lia.
Qed.
Fixpoint tower_column (order : nat) : cd_tower order -> matrix.matrix R (tower_dimension order) 1 :=
 match order as dimension return cd_tower dimension -> matrix.matrix R (tower_dimension dimension) 1 with
 | O => fun value => matrix.const_mx value
 | S lower => fun value => matrix.col_mx (tower_column lower (fst value)) (tower_column lower (snd value)) end.
Fixpoint column_tower (order : nat) : matrix.matrix R (tower_dimension order) 1 -> cd_tower order :=
 match order as dimension return matrix.matrix R (tower_dimension dimension) 1 -> cd_tower dimension with
 | O => fun value => value (@fintype.ord0 0) (@fintype.ord0 0)
 | S lower => fun value => (column_tower lower (matrix.usubmx value),column_tower lower (matrix.dsubmx value)) end.
Theorem column_tower_round_trip order : forall value,
 column_tower order (tower_column order value) = value.
Proof.
 induction order as [|order induction_equal]; intro value.
 - simpl. rw mxE. reflexivity.
 - destruct value; simpl. rw col_mxKu col_mxKd !induction_equal. reflexivity.
Qed.
Theorem tower_column_round_trip order : forall value,
 tower_column order (column_tower order value) = value.
Proof.
 induction order as [|order induction_equal]; intro value.
 - apply (proj1 (matrixP _ _)). intros row column.
   destruct row as [[|row] row_bound]; [|discriminate].
   destruct column as [[|column] column_bound]; [|discriminate].
   simpl. rw mxE. apply f_equal2; apply fintype.ord_inj; reflexivity.
 - simpl. rw !induction_equal vsubmxK. reflexivity.
Qed.
Theorem tower_column_injective order : forall first second,
 tower_column order first = tower_column order second -> first = second.
Proof.
 intros first second equal. apply (f_equal (column_tower order)) in equal.
 rw !column_tower_round_trip in equal. exact equal.
Qed.
Print Assumptions tower_column_round_trip.
Print Assumptions tower_column_injective.
Lemma tower_column_zero order : tower_column order (tower_zero order) = nmodule.Algebra.zero.
Proof.
 induction order as [|order induction_equal].
 - apply (proj1 (matrixP _ _)); intros row column. simpl. rw !mxE. reflexivity.
 - simpl. rw induction_equal col_mx0. reflexivity.
Qed.
Lemma tower_column_add order : forall first second,
 tower_column order (tower_add order first second) =
 nmodule.Algebra.add (tower_column order first) (tower_column order second).
Proof.
 induction order as [|order induction_equal]; intros first second.
 - apply (proj1 (matrixP _ _)); intros row column. simpl. rw !mxE. reflexivity.
 - destruct first, second; simpl. rw !induction_equal add_col_mx. reflexivity.
Qed.
Lemma tower_column_neg order : forall value,
 tower_column order (tower_neg order value) = nmodule.Algebra.opp (tower_column order value).
Proof.
 induction order as [|order induction_equal]; intro value.
 - apply (proj1 (matrixP _ _)); intros row column. simpl. rw !mxE. reflexivity.
 - destruct value; simpl. rw !induction_equal opp_col_mx. reflexivity.
Qed.
Lemma tower_column_scale order factor : forall value,
 tower_column order (tower_scale order factor value) = matrix.scalemx factor (tower_column order value).
Proof.
 induction order as [|order induction_equal]; intro value.
 - apply (proj1 (matrixP _ _)); intros row column. simpl. rw !mxE. reflexivity.
 - destruct value; simpl. rw !induction_equal.
   apply (proj1 (matrixP _ _)); intros row column. rw !mxE.
   case: (fintype.split row) => index; rw !mxE; reflexivity.
Qed.
Fixpoint tower_conjugation_matrix (order : nat) : matrix.matrix R (tower_dimension order) (tower_dimension order) :=
 match order as dimension return matrix.matrix R (tower_dimension dimension) (tower_dimension dimension) with
 | O => matrix.scalar_mx R1
 | S lower => matrix.block_mx (tower_conjugation_matrix lower) nmodule.Algebra.zero nmodule.Algebra.zero
   (nmodule.Algebra.opp (matrix.scalar_mx R1)) end.
Theorem tower_column_conjugation order : forall value,
 tower_column order (tower_conj order value) = matrix.mulmx (tower_conjugation_matrix order) (tower_column order value).
Proof.
 induction order as [|order induction_equal]; intro value.
 - simpl. rw mul1mx. reflexivity.
 - destruct value; simpl. rw induction_equal tower_column_neg mul_block_col
   ?mul0mx ?nmodule.Algebra.addr0 ?nmodule.Algebra.add0r mulNmx mul1mx. reflexivity.
Qed.
Theorem tower_conjugation_matrix_involution order :
 matrix.mulmx (tower_conjugation_matrix order) (tower_conjugation_matrix order) = matrix.scalar_mx R1.
Proof.
 induction order as [|order induction_equal].
 - simpl. rw mul1mx. reflexivity.
 - simpl. rw mulmx_block ?mul0mx ?mulmx0 ?nmodule.Algebra.add0r ?nmodule.Algebra.addr0
   induction_equal mulNmx mulmxN nmodule.Algebra.opprK mul1mx -scalar_mx_block. reflexivity.
Qed.
Print Assumptions tower_column_conjugation.
Print Assumptions tower_conjugation_matrix_involution.
Fixpoint tower_left_matrix (order : nat) : cd_tower order -> matrix.matrix R (tower_dimension order) (tower_dimension order) :=
 match order as dimension return cd_tower dimension -> matrix.matrix R (tower_dimension dimension) (tower_dimension dimension) with
 | O => fun operand => matrix.scalar_mx operand
 | S lower => fun operand => matrix.block_mx
   (tower_left_matrix lower (fst operand))
   (nmodule.Algebra.opp (matrix.mulmx (tower_right_matrix lower (snd operand)) (tower_conjugation_matrix lower)))
   (matrix.mulmx (tower_left_matrix lower (snd operand)) (tower_conjugation_matrix lower))
   (tower_right_matrix lower (fst operand)) end
with tower_right_matrix (order : nat) : cd_tower order -> matrix.matrix R (tower_dimension order) (tower_dimension order) :=
 match order as dimension return cd_tower dimension -> matrix.matrix R (tower_dimension dimension) (tower_dimension dimension) with
 | O => fun operand => matrix.scalar_mx operand
 | S lower => fun operand => matrix.block_mx
   (tower_right_matrix lower (fst operand))
   (nmodule.Algebra.opp (tower_left_matrix lower (tower_conj lower (snd operand))))
   (tower_left_matrix lower (snd operand))
   (tower_right_matrix lower (tower_conj lower (fst operand))) end.
Theorem tower_multiplication_matrices order :
 (forall first second, tower_column order (tower_mul order first second) =
   matrix.mulmx (tower_left_matrix order first) (tower_column order second)) /\
 (forall first second, tower_column order (tower_mul order first second) =
   matrix.mulmx (tower_right_matrix order second) (tower_column order first)).
Proof.
 induction order as [|order [left_action right_action]].
 - split; intros first second; apply (proj1 (matrixP _ _)); intros row column;
   simpl; rw mul_scalar_mx !mxE; [reflexivity|apply Rmult_comm].
 - split; intros [first_low first_high] [second_low second_high]; simpl; unfold tower_sub;
   rw !tower_column_add !tower_column_neg.
   + rw (left_action first_low second_low)
       (right_action (tower_conj order second_high) first_high)
       (right_action second_high first_low)
       (left_action first_high (tower_conj order second_low))
       !tower_column_conjugation mul_block_col mulNmx -!mulmxA.
     apply f_equal2; [reflexivity|exact (nmodule.Algebra.addrC _ _)].
   + rw (right_action first_low second_low)
       (left_action (tower_conj order second_high) first_high)
       (left_action second_high first_low)
       (right_action first_high (tower_conj order second_low))
       mul_block_col mulNmx. reflexivity.
Qed.
Print Assumptions tower_multiplication_matrices.
Lemma real_matrix_equal_on_columns rows columns
 (first second : matrix.matrix R rows columns) :
 (forall vector : matrix.matrix R columns 1, matrix.mulmx first vector = matrix.mulmx second vector) ->
 first = second.
Proof.
 intro equal. apply (proj1 (matrixP _ _)); intros row column.
 pose proof (equal (matrix.delta_mx column (@fintype.ord0 0))) as columns_equal.
 rw -!colE in columns_equal.
 exact (@matrix.col_eq R rows columns columns column column first second columns_equal row).
Qed.
Theorem tower_matrix_extensionality order
 (first second : matrix.matrix R (tower_dimension order) (tower_dimension order)) :
 (forall vector, matrix.mulmx first (tower_column order vector) = matrix.mulmx second (tower_column order vector)) ->
 first = second.
Proof.
 intro equal. apply real_matrix_equal_on_columns. intro vector.
 pose proof (equal (column_tower order vector)) as encoded_equal.
 rw !tower_column_round_trip in encoded_equal. exact encoded_equal.
Qed.
Theorem tower_zero_multiplication_matrices order :
 tower_left_matrix order (tower_zero order) = nmodule.Algebra.zero /\
 tower_right_matrix order (tower_zero order) = nmodule.Algebra.zero.
Proof.
 split; apply tower_matrix_extensionality; intro vector; rw mul0mx.
 - rw -(proj1 (tower_multiplication_matrices order) (tower_zero order) vector)
   tower_mul_zero_left tower_column_zero. reflexivity.
 - rw -(proj2 (tower_multiplication_matrices order) vector (tower_zero order))
   tower_mul_zero_right tower_column_zero. reflexivity.
Qed.
Print Assumptions tower_zero_multiplication_matrices.
