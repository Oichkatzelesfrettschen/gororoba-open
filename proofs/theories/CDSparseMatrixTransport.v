(** Complete coordinate decoders transport sparse CD sector ranks. *)
From Stdlib Require Import Arith Bool.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import SchreierSignCode CDAssociatorDoubling CDSignNumericCorrespondence CubeAffineCosets FiniteMatrixConventions.
Import ssreflect divalg matrix mxalgebra rat.
Set Implicit Arguments.
Section SparseField.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Variable order : nat.
Variable group : xor_subgroup order.
Variable anchor : cube order.
Definition scalar_phase (phase : bool) : scalar :=
  if phase then nmodule.Algebra.opp (@rings_modules_and_algebras.GRing.one scalar)
  else @rings_modules_and_algebras.GRing.one scalar.
Definition field_affine_supported (operand : cube order -> scalar) :=
  forall input, same_coset order group input anchor = false -> operand input = nmodule.Algebra.zero.
Definition sparse_field_entry (operand : cube order -> scalar) (output input : cube order) : scalar :=
  rings_modules_and_algebras.GRing.mul (operand (cube_xor order output input))
    (scalar_phase (sign_exponent order (cube_xor order output input) input)).
Lemma sparse_field_cross_zero operand output input : field_affine_supported operand ->
  same_coset order group output (cube_xor order anchor input) = false ->
  sparse_field_entry operand output input = nmodule.Algebra.zero.
Proof.
  move=> supported cross.
  assert (outside : same_coset order group (cube_xor order output input) anchor = false).
  { unfold same_coset in *. rw -cube_xor_associative (cube_xor_commutative order input anchor). exact cross. }
  unfold sparse_field_entry. rw (supported _ outside). exact (@rings_modules_and_algebras.GRing.mul0r scalar _).
Qed.
Definition sparse_field_matrix operand : matrix.matrix scalar (Nat.pow 2 order) (Nat.pow 2 order) :=
  @matrix.matrix_of_fun scalar (Nat.pow 2 order) (Nat.pow 2 order) matrix.matrix_key (fun output input =>
    sparse_field_entry operand (cube_decode order (fintype.nat_of_ord output))
      (cube_decode order (fintype.nat_of_ord input))).
Variables rows_left rows_right columns_left columns_right : nat.
Variable row_map : fintype.ordinal (ssrnat.addn rows_left rows_right) -> fintype.ordinal (Nat.pow 2 order).
Variable column_map : fintype.ordinal (ssrnat.addn columns_left columns_right) -> fintype.ordinal (Nat.pow 2 order).
Variable sector : cube order.
Definition sector_row_input row := cube_decode order (fintype.nat_of_ord (row_map row)).
Definition sector_column_input column := cube_decode order (fintype.nat_of_ord (column_map column)).
Definition row_sector_coordinates :=
  (forall row : fintype.ordinal rows_left,
    same_coset order group (sector_row_input (@fintype.lshift rows_left rows_right row))
      (cube_xor order anchor sector) = true) /\
  (forall row : fintype.ordinal rows_right,
    same_coset order group (sector_row_input (@fintype.rshift rows_left rows_right row))
      (cube_xor order anchor sector) = false).
Definition column_sector_coordinates :=
  (forall column : fintype.ordinal columns_left,
    same_coset order group (sector_column_input (@fintype.lshift columns_left columns_right column)) sector = true) /\
  (forall column : fintype.ordinal columns_right,
    same_coset order group (sector_column_input (@fintype.rshift columns_left columns_right column)) sector = false).
Lemma sparse_field_upper_cross_zero operand : field_affine_supported operand ->
  row_sector_coordinates -> column_sector_coordinates ->
  matrix.ursubmx (matrix.mxsub row_map column_map (sparse_field_matrix operand)) =
    matrix_zero scalar rows_left columns_right.
Proof.
  move=> supported [upper_rows lower_rows] [upper_columns lower_columns].
  apply (proj1 (matrix.matrixP _ _)). intros row column.
  unfold sparse_field_matrix, matrix_zero. rw matrix.ursubmxEsub !matrix.mxE.
  apply sparse_field_cross_zero; [exact supported|].
  change (same_coset order group (sector_row_input (@fintype.lshift rows_left rows_right row))
    (cube_xor order anchor (sector_column_input (@fintype.rshift columns_left columns_right column))) = false).
  destruct (same_coset order group (sector_row_input (@fintype.lshift rows_left rows_right row))
    (cube_xor order anchor (sector_column_input (@fintype.rshift columns_left columns_right column)))) eqn:cross; [|reflexivity].
  pose proof (same_coset_equivalent_left order group _ _ (cube_xor order anchor sector) cross) as equivalent.
  rw same_coset_translation (upper_rows row) (lower_columns column) in equivalent. discriminate.
Qed.
Lemma sparse_field_lower_cross_zero operand : field_affine_supported operand ->
  row_sector_coordinates -> column_sector_coordinates ->
  matrix.dlsubmx (matrix.mxsub row_map column_map (sparse_field_matrix operand)) =
    matrix_zero scalar rows_right columns_left.
Proof.
  move=> supported [upper_rows lower_rows] [upper_columns lower_columns].
  apply (proj1 (matrix.matrixP _ _)). intros row column.
  unfold sparse_field_matrix, matrix_zero. rw matrix.dlsubmxEsub !matrix.mxE.
  apply sparse_field_cross_zero; [exact supported|].
  change (same_coset order group (sector_row_input (@fintype.rshift rows_left rows_right row))
    (cube_xor order anchor (sector_column_input (@fintype.lshift columns_left columns_right column))) = false).
  destruct (same_coset order group (sector_row_input (@fintype.rshift rows_left rows_right row))
    (cube_xor order anchor (sector_column_input (@fintype.lshift columns_left columns_right column)))) eqn:cross; [|reflexivity].
  pose proof (same_coset_equivalent_left order group _ _ (cube_xor order anchor sector) cross) as equivalent.
  rw same_coset_translation (lower_rows row) (upper_columns column) in equivalent. discriminate.
Qed.
Theorem sparse_field_block_decomposition operand : field_affine_supported operand ->
  row_sector_coordinates -> column_sector_coordinates ->
  matrix.mxsub row_map column_map (sparse_field_matrix operand) =
  matrix.block_mx (matrix.ulsubmx (matrix.mxsub row_map column_map (sparse_field_matrix operand)))
    (matrix_zero scalar rows_left columns_right) (matrix_zero scalar rows_right columns_left)
    (matrix.drsubmx (matrix.mxsub row_map column_map (sparse_field_matrix operand))).
Proof.
  move=> supported row_coordinates column_coordinates. apply zero_cross_block_decomposition.
  - apply sparse_field_upper_cross_zero; assumption.
  - apply sparse_field_lower_cross_zero; assumption.
Qed.
Theorem sparse_field_rank_decomposition operand
  (row_back : fintype.ordinal (Nat.pow 2 order) -> fintype.ordinal (ssrnat.addn rows_left rows_right))
  (column_back : fintype.ordinal (Nat.pow 2 order) -> fintype.ordinal (ssrnat.addn columns_left columns_right)) :
  field_affine_supported operand -> row_sector_coordinates -> column_sector_coordinates ->
  (forall row, row_map (row_back row) = row) ->
  (forall column, column_map (column_back column) = column) ->
  mxalgebra.mxrank (sparse_field_matrix operand) = ssrnat.addn
    (mxalgebra.mxrank (matrix.ulsubmx (matrix.mxsub row_map column_map (sparse_field_matrix operand))))
    (mxalgebra.mxrank (matrix.drsubmx (matrix.mxsub row_map column_map (sparse_field_matrix operand)))).
Proof.
  move=> supported row_coordinates column_coordinates rows_complete columns_complete.
  rw -(@complete_reindex_rank scalar (Nat.pow 2 order) (Nat.pow 2 order) (ssrnat.addn rows_left rows_right) (ssrnat.addn columns_left columns_right) (sparse_field_matrix operand) row_map column_map row_back column_back rows_complete columns_complete).
  apply zero_cross_rank_decomposition.
  - apply sparse_field_upper_cross_zero; assumption.
  - apply sparse_field_lower_cross_zero; assumption.
Qed.
End SparseField.
Print Assumptions sparse_field_block_decomposition.
Print Assumptions sparse_field_rank_decomposition.
