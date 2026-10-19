(** Arbitrary real coefficients use the same highest-bit, column-action
    convention as the Boolean and numeric basis multiplication laws. *)
From Stdlib Require Import Reals Bool Lia.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import RecursiveCDTower CDTowerMatrixAdapter
 CDTowerSignCorrespondence CDSparseMatrixTransport CDPhaseDegree SchreierSignCode
 StdlibRealFieldAdapter CDSignNumericCorrespondence RationalRealSpecialization.
Import ssreflect ssrbool matrix divalg fintype.
Import GRing.Theory.
Open Scope R_scope.

Fixpoint tower_coordinate order : cd_tower order -> cube order -> R :=
 match order as dimension return cd_tower dimension -> cube dimension -> R with
 | O => fun value _ => value
 | S lower => fun value index =>
   tower_coordinate lower (if snd index then snd value else fst value) (fst index)
 end.

Lemma tower_coordinate_zero order : forall index,
 tower_coordinate order (tower_zero order) index = 0.
Proof.
 induction order as [|order induction_equal]; intro index; [reflexivity|].
 destruct index as [index high]; destruct high; simpl; apply induction_equal.
Qed.
Lemma tower_coordinate_add order : forall first second index,
 tower_coordinate order (tower_add order first second) index =
 tower_coordinate order first index + tower_coordinate order second index.
Proof.
 induction order as [|order induction_equal]; intros first second index; [reflexivity|].
 destruct first, second, index as [index high]; destruct high; simpl; apply induction_equal.
Qed.
Lemma tower_coordinate_scale order factor : forall value index,
 tower_coordinate order (tower_scale order factor value) index =
 factor * tower_coordinate order value index.
Proof.
 induction order as [|order induction_equal]; intros value index; [reflexivity|].
 destruct value, index as [index high]; destruct high; simpl; apply induction_equal.
Qed.
Lemma tower_coordinate_neg order : forall value index,
 tower_coordinate order (tower_neg order value) index = - tower_coordinate order value index.
Proof.
 induction order as [|order induction_equal]; intros value index; [reflexivity|].
 destruct value, index as [index high]; destruct high; simpl; apply induction_equal.
Qed.
Lemma tower_coordinate_basis order : forall basis index,
 tower_coordinate order (tower_basis order basis) index =
 if cube_equal order basis index then 1 else 0.
Proof.
 induction order as [|order induction_equal]; intros basis index.
 - destruct basis, index; reflexivity.
 - destruct basis as [basis basis_high], index as [index index_high].
   destruct basis_high, index_high; simpl;
     rw ?induction_equal ?tower_coordinate_zero;
     destruct (cube_equal order basis index); reflexivity.
Qed.

Definition tower_real_linear order (function : cd_tower order -> R) :=
 (forall first second, function (tower_add order first second) = function first + function second) /\
 (forall factor value, function (tower_scale order factor value) = factor * function value).

Theorem tower_linear_basis_extensionality order :
 forall (first second : cd_tower order -> R),
 tower_real_linear order first -> tower_real_linear order second ->
 (forall index, first (tower_basis order index) = second (tower_basis order index)) ->
 forall value, first value = second value.
Proof.
 induction order as [|order induction_equal]; intros first second
   [first_add first_scale] [second_add second_scale] basis_equal value.
 - pose proof (first_scale value 1) as first_scalar.
   pose proof (second_scale value 1) as second_scalar.
   simpl in first_scalar, second_scalar.
   rw Rmult_1_r in first_scalar second_scalar.
   rw first_scalar second_scalar.
   pose proof (basis_equal tt) as equal; simpl in equal. rw equal. reflexivity.
 - destruct value as [low high].
   assert (low_equal : forall value,
     first (value,tower_zero order) = second (value,tower_zero order)).
   { apply induction_equal.
     - split.
       + intros left right. specialize (first_add (left,tower_zero order) (right,tower_zero order)).
         simpl in first_add. rw tower_add_zero in first_add. exact first_add.
       + intros factor value. specialize (first_scale factor (value,tower_zero order)).
         simpl in first_scale. rw tower_scale_zero in first_scale. exact first_scale.
     - split.
       + intros left right. specialize (second_add (left,tower_zero order) (right,tower_zero order)).
         simpl in second_add. rw tower_add_zero in second_add. exact second_add.
       + intros factor value. specialize (second_scale factor (value,tower_zero order)).
         simpl in second_scale. rw tower_scale_zero in second_scale. exact second_scale.
     - intro index. exact (basis_equal (index,false)). }
   assert (high_equal : forall value,
     first (tower_zero order,value) = second (tower_zero order,value)).
   { apply induction_equal.
     - split.
       + intros left right. specialize (first_add (tower_zero order,left) (tower_zero order,right)).
         simpl in first_add. rw tower_add_zero in first_add. exact first_add.
       + intros factor value. specialize (first_scale factor (tower_zero order,value)).
         simpl in first_scale. rw tower_scale_zero in first_scale. exact first_scale.
     - split.
       + intros left right. specialize (second_add (tower_zero order,left) (tower_zero order,right)).
         simpl in second_add. rw tower_add_zero in second_add. exact second_add.
       + intros factor value. specialize (second_scale factor (tower_zero order,value)).
         simpl in second_scale. rw tower_scale_zero in second_scale. exact second_scale.
     - intro index. exact (basis_equal (index,true)). }
   assert (decomposition : (low,high) = tower_add (S order)
       (low,tower_zero order) (tower_zero order,high)).
   { simpl. rw tower_add_comm !tower_add_zero. reflexivity. }
   rw decomposition first_add second_add low_equal high_equal. reflexivity.
Qed.

Lemma tower_multiplication_add_left order first second right :
 tower_mul order (tower_add order first second) right =
 tower_add order (tower_mul order first right) (tower_mul order second right).
Proof.
 apply tower_column_injective.
 rw tower_column_add.
 rw !(proj2 (tower_multiplication_matrices order)) tower_column_add.
 rw matrix.mulmxDr. reflexivity.
Qed.
Lemma tower_multiplication_scale_left order factor first right :
 tower_mul order (tower_scale order factor first) right =
 tower_scale order factor (tower_mul order first right).
Proof.
 apply tower_column_injective.
 rw tower_column_scale.
 rw !(proj2 (tower_multiplication_matrices order)) tower_column_scale.
 rw -matrix.scalemxAr. reflexivity.
Qed.

Definition real_sign phase : R := if phase then -1 else 1.
Theorem tower_product_basis_coordinate order : forall operand input output,
 tower_coordinate order (tower_mul order operand (tower_basis order input)) output =
 tower_coordinate order operand (cube_xor order output input) *
 real_sign (sign_exponent order (cube_xor order output input) input).
Proof.
 intros operand input output.
 apply (tower_linear_basis_extensionality order
   (fun value => tower_coordinate order (tower_mul order value (tower_basis order input)) output)
   (fun value => tower_coordinate order value (cube_xor order output input) *
     real_sign (sign_exponent order (cube_xor order output input) input))).
 - split.
   + intros first second. rw tower_multiplication_add_left tower_coordinate_add. reflexivity.
   + intros factor value. rw tower_multiplication_scale_left tower_coordinate_scale. reflexivity.
 - split.
   + intros first second. rw tower_coordinate_add. ring.
   + intros factor value. rw tower_coordinate_scale. ring.
 - intro basis. rw tower_basis_multiplication.
   unfold tower_signed. destruct (sign_exponent order basis input) eqn:phase;
     rw ?tower_coordinate_neg !tower_coordinate_basis.
   + destruct (cube_equal order basis (cube_xor order output input)) eqn:matches.
     * apply cube_equal_spec in matches. subst basis.
       rw cube_xor_right_cancel cube_equal_reflexive phase. unfold real_sign. ring.
     * assert (different : cube_equal order (cube_xor order basis input) output = false).
       { destruct (cube_equal order (cube_xor order basis input) output) eqn:equal; [|reflexivity].
         apply cube_equal_spec in equal. subst output.
         rw cube_xor_right_cancel cube_equal_reflexive in matches. discriminate. }
       rw different. ring.
   + destruct (cube_equal order basis (cube_xor order output input)) eqn:matches.
     * apply cube_equal_spec in matches. subst basis.
       rw cube_xor_right_cancel cube_equal_reflexive phase. unfold real_sign. ring.
     * assert (different : cube_equal order (cube_xor order basis input) output = false).
       { destruct (cube_equal order (cube_xor order basis input) output) eqn:equal; [|reflexivity].
         apply cube_equal_spec in equal. subst output.
         rw cube_xor_right_cancel cube_equal_reflexive in matches. discriminate. }
       rw different. ring.
Qed.

Print Assumptions tower_linear_basis_extensionality.
Print Assumptions tower_product_basis_coordinate.

Fixpoint cube_tower_index order : cube order -> fintype.ordinal (tower_dimension order) :=
 match order as dimension return cube dimension -> fintype.ordinal (tower_dimension dimension) with
 | O => fun _ => @fintype.ord0 0
 | S lower => fun index => if snd index
   then @fintype.rshift (tower_dimension lower) (tower_dimension lower) (cube_tower_index lower (fst index))
   else @fintype.lshift (tower_dimension lower) (tower_dimension lower) (cube_tower_index lower (fst index))
 end.

Lemma cube_tower_index_encoding order : forall index,
 fintype.nat_of_ord (cube_tower_index order index) = cube_encode order index.
Proof.
 induction order as [|order induction_equal]; intro index.
 - destruct index; reflexivity.
 - destruct index as [index high]; destruct high; simpl.
   + change ((tower_dimension order + fintype.nat_of_ord (cube_tower_index order index))%nat =
       (cube_encode order index + Nat.pow 2 order)%nat).
     rw induction_equal tower_dimension_power. lia.
   + rw induction_equal. lia.
Qed.

Lemma cube_tower_index_injective order first second :
 cube_tower_index order first = cube_tower_index order second -> first = second.
Proof.
 intro equal. apply cube_encode_injective.
 apply (f_equal (fun index : fintype.ordinal (tower_dimension order) => fintype.nat_of_ord index)) in equal.
 rw !cube_tower_index_encoding in equal. exact equal.
Qed.

Lemma cube_tower_index_decode order (index : fintype.ordinal (tower_dimension order)) :
 cube_tower_index order (cube_decode order (fintype.nat_of_ord index)) = index.
Proof.
 assert (bounded : (fintype.nat_of_ord index < Nat.pow 2 order)%nat).
 { rw -tower_dimension_power. apply (elimT ssrnat.leP). exact (fintype.ltn_ord index). }
 apply fintype.ord_inj. rw cube_tower_index_encoding (cube_encode_decode order _ bounded). reflexivity.
Qed.

Lemma cube_tower_index_equal order first second :
 eqtype.eq_op (cube_tower_index order first) (cube_tower_index order second) =
 cube_equal order first second.
Proof.
 destruct (cube_equal order first second) eqn:equal.
 - apply cube_equal_spec in equal. subst second. exact: eqtype.eqxx.
 - destruct (eqtype.eq_op (cube_tower_index order first) (cube_tower_index order second)) eqn:indices; [|reflexivity].
   apply (elimT eqtype.eqP) in indices. apply cube_tower_index_injective in indices.
   subst second. rw cube_equal_reflexive in equal. discriminate.
Qed.

Theorem tower_coordinate_column order : forall value index,
 tower_column order value (cube_tower_index order index) (@fintype.ord0 0) =
 tower_coordinate order value index.
Proof.
 induction order as [|order induction_equal]; intros value index.
 - simpl. rw matrix.mxE. reflexivity.
 - destruct value as [low high], index as [index high_bit]; destruct high_bit; simpl.
   + rw matrix.col_mxEd. exact (induction_equal high index).
   + rw matrix.col_mxEu. exact (induction_equal low index).
Qed.

Theorem tower_basis_column order index :
 tower_column order (tower_basis order index) =
 matrix.delta_mx (cube_tower_index order index) (@fintype.ord0 0).
Proof.
 apply (proj1 (matrix.matrixP _ _)); intros row column.
 assert (column_zero : column = @fintype.ord0 0).
 { apply fintype.ord_inj. pose proof (elimT ssrnat.leP (fintype.ltn_ord column)). simpl in *. lia. }
 subst column. rw -(cube_tower_index_decode order row) tower_coordinate_column tower_coordinate_basis matrix.mxE.
 rw cube_tower_index_equal eqtype.eqxx Bool.andb_true_r cube_equal_symmetric.
 destruct (cube_equal order (cube_decode order row) index); reflexivity.
Qed.

Theorem tower_left_matrix_coordinate order operand output input :
 tower_left_matrix order operand (cube_tower_index order output) (cube_tower_index order input) =
 tower_coordinate order operand (cube_xor order output input) *
 real_sign (sign_exponent order (cube_xor order output input) input).
Proof.
 pose proof (proj1 (tower_multiplication_matrices order) operand (tower_basis order input)) as action.
 rw tower_basis_column -matrix.colE in action.
 apply (f_equal (fun column : matrix.matrix R (tower_dimension order) 1 =>
   column (cube_tower_index order output) (@fintype.ord0 0))) in action.
 rw tower_coordinate_column matrix.mxE in action.
 rw -action. apply tower_product_basis_coordinate.
Qed.

Print Assumptions cube_tower_index_decode.
Print Assumptions tower_left_matrix_coordinate.

Theorem tower_left_matrix_numeric_coordinate order operand
 (output input : fintype.ordinal (tower_dimension order)) :
 tower_left_matrix order operand output input =
 tower_coordinate order operand
   (cube_xor order (cube_decode order output) (cube_decode order input)) *
 real_sign (sign_exponent order
   (cube_xor order (cube_decode order output) (cube_decode order input))
   (cube_decode order input)).
Proof.
 pose proof (tower_left_matrix_coordinate order operand
   (cube_decode order output) (cube_decode order input)) as entry.
 rw !cube_tower_index_decode in entry. exact entry.
Qed.

Lemma tower_cast_index_value first_size second_size (equal : first_size = second_size)
 (index : fintype.ordinal first_size) :
 fintype.nat_of_ord (fintype.cast_ord equal index) = fintype.nat_of_ord index.
Proof. destruct equal. reflexivity. Qed.

Theorem sparse_tower_left_matrix_correspondence order operand :
 matrix.castmx (tower_dimension_power order,tower_dimension_power order)
   (tower_left_matrix order operand) =
 @sparse_field_matrix stdlib_real_field order (tower_coordinate order operand).
Proof.
 apply (proj1 (matrix.matrixP _ _)); intros output input.
 rw matrix.castmxE tower_left_matrix_numeric_coordinate !tower_cast_index_value.
 unfold sparse_field_matrix, sparse_field_entry. rw matrix.mxE.
 unfold real_sign, scalar_phase.
 destruct (sign_exponent order
   (cube_xor order (cube_decode order output) (cube_decode order input))
   (cube_decode order input)); reflexivity.
Qed.

Print Assumptions tower_left_matrix_numeric_coordinate.
Print Assumptions sparse_tower_left_matrix_correspondence.

Fixpoint tower_from_coordinates order : (cube order -> R) -> cd_tower order :=
 match order as dimension return (cube dimension -> R) -> cd_tower dimension with
 | O => fun coefficients => coefficients tt
 | S lower => fun coefficients =>
   (tower_from_coordinates lower (fun index => coefficients (index,false)),
    tower_from_coordinates lower (fun index => coefficients (index,true)))
 end.

Lemma tower_from_coordinates_round_trip order : forall coefficients index,
 tower_coordinate order (tower_from_coordinates order coefficients) index = coefficients index.
Proof.
 induction order as [|order induction_equal]; intros coefficients index.
 - destruct index; reflexivity.
 - destruct index as [index high]; destruct high; simpl; apply induction_equal.
Qed.

Theorem sparse_rational_real_map order (coefficients : cube order -> rat.rat) :
 matrix.map_mx real_rational (@sparse_field_matrix mathcomp_rational_field order coefficients) =
 @sparse_field_matrix stdlib_real_field order (fun index => real_rational (coefficients index)).
Proof.
 apply (proj1 (matrix.matrixP _ _)); intros output input.
 unfold sparse_field_matrix, sparse_field_entry. rw !matrix.mxE rmorphM.
 unfold scalar_phase.
 set (coefficient := coefficients
   (cube_xor order (cube_decode order output) (cube_decode order input))).
 destruct (sign_exponent order
   (cube_xor order (cube_decode order output) (cube_decode order input))
   (cube_decode order input)).
 - change (real_rational coefficient * real_rational (rat.ratz (ssrint.Negz 0)) =
     real_rational coefficient * (-1))%R.
   rw real_rational_integer. simpl. ring.
 - change (real_rational coefficient * real_rational (rat.ratz (ssrint.Posz 1)) =
     real_rational coefficient * 1)%R.
   rw real_rational_integer. simpl. ring.
Qed.

Theorem rational_sparse_tower_matrix order (coefficients : cube order -> rat.rat) :
 matrix.castmx (tower_dimension_power order,tower_dimension_power order)
   (tower_left_matrix order
     (tower_from_coordinates order (fun index => real_rational (coefficients index)))) =
 matrix.map_mx real_rational (@sparse_field_matrix mathcomp_rational_field order coefficients).
Proof.
 rw sparse_tower_left_matrix_correspondence sparse_rational_real_map.
 apply (proj1 (matrix.matrixP _ _)); intros output input.
 unfold sparse_field_matrix, sparse_field_entry. rw !matrix.mxE tower_from_coordinates_round_trip. reflexivity.
Qed.

Lemma matrix_cast_preserves_rank rows columns mapped_rows mapped_columns
 (equal : (rows = mapped_rows) * (columns = mapped_columns))
 (operator : matrix.matrix R rows columns) :
 @mxalgebra.mxrank stdlib_real_field mapped_rows mapped_columns (matrix.castmx equal operator) =
 @mxalgebra.mxrank stdlib_real_field rows columns operator.
Proof.
 destruct equal as [rows_equal columns_equal]. destruct rows_equal, columns_equal.
 rw matrix.castmx_id. reflexivity.
Qed.

Theorem rational_sparse_tower_rank order (coefficients : cube order -> rat.rat) :
 @mxalgebra.mxrank stdlib_real_field (tower_dimension order) (tower_dimension order)
   (tower_left_matrix order
     (tower_from_coordinates order (fun index => real_rational (coefficients index)))) =
 @mxalgebra.mxrank mathcomp_rational_field (Nat.pow 2 order) (Nat.pow 2 order)
   (@sparse_field_matrix mathcomp_rational_field order coefficients).
Proof.
 rw -(matrix_cast_preserves_rank _ _ _ _
   (tower_dimension_power order,tower_dimension_power order))
   rational_sparse_tower_matrix actual_rational_real_rank. reflexivity.
Qed.

Print Assumptions sparse_rational_real_map.
Print Assumptions rational_sparse_tower_matrix.
Print Assumptions rational_sparse_tower_rank.
