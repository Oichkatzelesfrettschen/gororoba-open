(** Repository operators act on columns; MathComp row kernels use transpose. *)
From Stdlib Require Import Arith List.
From mathcomp Require boot order algebra.
Import ssreflect divalg matrix mxalgebra rat.
Set Implicit Arguments.
Section ColumnConventions.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Definition matrix_zero rows columns : matrix.matrix scalar rows columns := nmodule.Algebra.zero.
Theorem right_kernel_transpose rows columns (operator : matrix.matrix scalar rows columns)
  (vector : matrix.matrix scalar columns 1) :
  matrix.mulmx operator vector = matrix_zero rows 1 <->
  matrix.mulmx (matrix.trmx vector) (matrix.trmx operator) = matrix_zero 1 rows.
Proof.
  split => residual.
  - rw -matrix.trmx_mul residual matrix.trmx0. reflexivity.
  - apply (f_equal matrix.trmx) in residual.
    rw matrix.trmx_mul !matrix.trmxK matrix.trmx0 in residual. exact residual.
Qed.
Theorem column_kernel_residual rows columns (operator : matrix.matrix scalar rows columns) :
  matrix.mulmx operator (matrix.trmx (mxalgebra.kermx (matrix.trmx operator))) = matrix_zero rows columns.
Proof.
  pose proof (mxalgebra.mulmx_ker (matrix.trmx operator)) as residual.
  apply (f_equal matrix.trmx) in residual.
  rw matrix.trmx_mul matrix.trmxK matrix.trmx0 in residual. exact residual.
Qed.
End ColumnConventions.

Section BlockConventions.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Theorem block_column_kernel rows_left rows_right columns_left columns_right
  (left : matrix.matrix scalar rows_left columns_left) (right : matrix.matrix scalar rows_right columns_right)
  (upper : matrix.matrix scalar columns_left 1) (lower : matrix.matrix scalar columns_right 1) :
  matrix.mulmx (matrix.block_mx left (matrix_zero scalar rows_left columns_right)
    (matrix_zero scalar rows_right columns_left) right) (matrix.col_mx upper lower) =
    matrix_zero scalar (ssrnat.addn rows_left rows_right) 1 <->
  matrix.mulmx left upper = matrix_zero scalar rows_left 1 /\
  matrix.mulmx right lower = matrix_zero scalar rows_right 1.
Proof.
  unfold matrix_zero. rw matrix.mul_block_col !matrix.mul0mx nmodule.Algebra.addr0 nmodule.Algebra.add0r.
  split => residual.
  - apply matrix.eq_col_mx. rw matrix.col_mx0. exact residual.
  - case: residual => upper_zero lower_zero. rw upper_zero lower_zero matrix.col_mx0. reflexivity.
Qed.
Theorem block_rank_decomposition rows_left rows_right columns_left columns_right
  (left : matrix.matrix scalar rows_left columns_left) (right : matrix.matrix scalar rows_right columns_right) :
  mxalgebra.mxrank (matrix.block_mx left (matrix_zero scalar rows_left columns_right)
    (matrix_zero scalar rows_right columns_left) right) =
  ssrnat.addn (mxalgebra.mxrank left) (mxalgebra.mxrank right).
Proof. exact: mxalgebra.rank_diag_block_mx. Qed.
Theorem left_inverse_reflects_zero rows columns width
  (forward : matrix.matrix scalar rows columns) (backward : matrix.matrix scalar columns rows)
  (value : matrix.matrix scalar columns width) :
  matrix.mulmx backward forward = matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar) ->
  (matrix.mulmx forward value = matrix_zero scalar rows width <-> value = matrix_zero scalar columns width).
Proof.
  move=> inverse. split => residual.
  - pose proof (f_equal (matrix.mulmx backward) residual) as cancelled.
    unfold matrix_zero in *. rw matrix.mulmxA inverse matrix.mul1mx matrix.mulmx0 in cancelled. exact cancelled.
  - rw residual matrix.mulmx0. reflexivity.
Qed.
End BlockConventions.
Print Assumptions right_kernel_transpose.
Print Assumptions column_kernel_residual.
Print Assumptions block_column_kernel.
Print Assumptions block_rank_decomposition.
Print Assumptions left_inverse_reflects_zero.

Section CoordinateTransport.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Lemma rank_sandwich_bound outer_rows inner_rows inner_columns outer_columns
  (left : matrix.matrix scalar outer_rows inner_rows) (middle : matrix.matrix scalar inner_rows inner_columns)
  (right : matrix.matrix scalar inner_columns outer_columns) :
  mxalgebra.mxrank (matrix.mulmx (matrix.mulmx left middle) right) <= mxalgebra.mxrank middle.
Proof.
  apply Nat.le_trans with (mxalgebra.mxrank (matrix.mulmx left middle)).
  - apply (ssrbool.elimT (@ssrnat.leP _ _)). exact: mxalgebra.mxrankM_maxl.
  - apply (ssrbool.elimT (@ssrnat.leP _ _)). exact: mxalgebra.mxrankM_maxr.
Qed.
Theorem inverse_coordinate_rank rows columns mapped_rows mapped_columns
  (operator : matrix.matrix scalar rows columns) (mapped : matrix.matrix scalar mapped_rows mapped_columns)
  (left : matrix.matrix scalar mapped_rows rows) (right : matrix.matrix scalar columns mapped_columns)
  (left_back : matrix.matrix scalar rows mapped_rows) (right_back : matrix.matrix scalar mapped_columns columns) :
  mapped = matrix.mulmx (matrix.mulmx left operator) right ->
  operator = matrix.mulmx (matrix.mulmx left_back mapped) right_back ->
  mxalgebra.mxrank mapped = mxalgebra.mxrank operator.
Proof.
  move=> forward backward. apply Nat.le_antisymm.
  - rw forward. apply rank_sandwich_bound.
  - rw backward. apply rank_sandwich_bound.
Qed.
Theorem coordinate_kernel_transport rows columns
  (operator : matrix.matrix scalar rows columns)
  (left left_back : matrix.matrix scalar rows rows)
  (right : matrix.matrix scalar columns columns) (vector : matrix.matrix scalar columns 1) :
  matrix.mulmx left_back left = matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar) ->
  (matrix.mulmx (matrix.mulmx (matrix.mulmx left operator) right) vector = matrix_zero scalar rows 1 <->
   matrix.mulmx operator (matrix.mulmx right vector) = matrix_zero scalar rows 1).
Proof.
  move=> inverse. rw -!matrix.mulmxA. exact (@left_inverse_reflects_zero scalar rows rows 1 left left_back (matrix.mulmx operator (matrix.mulmx right vector)) inverse).
Qed.
Theorem diagonal_coordinate_rank rows_left rows_right columns_left columns_right rows columns
  (operator : matrix.matrix scalar rows columns)
  (upper : matrix.matrix scalar rows_left columns_left) (lower : matrix.matrix scalar rows_right columns_right)
  (left : matrix.matrix scalar (ssrnat.addn rows_left rows_right) rows)
  (right : matrix.matrix scalar columns (ssrnat.addn columns_left columns_right))
  (left_back : matrix.matrix scalar rows (ssrnat.addn rows_left rows_right))
  (right_back : matrix.matrix scalar (ssrnat.addn columns_left columns_right) columns) :
  matrix.block_mx upper (matrix_zero scalar rows_left columns_right)
    (matrix_zero scalar rows_right columns_left) lower = matrix.mulmx (matrix.mulmx left operator) right ->
  operator = matrix.mulmx (matrix.mulmx left_back
    (matrix.block_mx upper (matrix_zero scalar rows_left columns_right)
      (matrix_zero scalar rows_right columns_left) lower)) right_back ->
  mxalgebra.mxrank operator = ssrnat.addn (mxalgebra.mxrank upper) (mxalgebra.mxrank lower).
Proof.
  move=> forward backward. rw -(inverse_coordinate_rank forward backward). apply block_rank_decomposition.
Qed.
End CoordinateTransport.
Print Assumptions inverse_coordinate_rank.
Print Assumptions coordinate_kernel_transport.
Print Assumptions diagonal_coordinate_rank.

Section ZeroCrossBlocks.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Theorem zero_cross_block_decomposition rows_left rows_right columns_left columns_right
  (operator : matrix.matrix scalar (ssrnat.addn rows_left rows_right) (ssrnat.addn columns_left columns_right)) :
  matrix.ursubmx operator = matrix_zero scalar rows_left columns_right ->
  matrix.dlsubmx operator = matrix_zero scalar rows_right columns_left ->
  operator = matrix.block_mx (matrix.ulsubmx operator) (matrix_zero scalar rows_left columns_right)
    (matrix_zero scalar rows_right columns_left) (matrix.drsubmx operator).
Proof. move=> upper_zero lower_zero. rw -upper_zero -lower_zero matrix.submxK. reflexivity. Qed.
Theorem zero_cross_rank_decomposition rows_left rows_right columns_left columns_right
  (operator : matrix.matrix scalar (ssrnat.addn rows_left rows_right) (ssrnat.addn columns_left columns_right)) :
  matrix.ursubmx operator = matrix_zero scalar rows_left columns_right ->
  matrix.dlsubmx operator = matrix_zero scalar rows_right columns_left ->
  mxalgebra.mxrank operator = ssrnat.addn (mxalgebra.mxrank (matrix.ulsubmx operator))
    (mxalgebra.mxrank (matrix.drsubmx operator)).
Proof.
  move=> upper_zero lower_zero. rw (zero_cross_block_decomposition upper_zero lower_zero) matrix.block_mxKul matrix.block_mxKdr.
  apply block_rank_decomposition.
Qed.
End ZeroCrossBlocks.
Print Assumptions zero_cross_block_decomposition.
Print Assumptions zero_cross_rank_decomposition.

Definition rational_phase_sign (phase : bool) : rat.rat :=
  rat.ratz (if phase then ssrint.Negz 0 else ssrint.Posz 1).
Definition rational_sign_block first second third fourth : matrix.matrix rat.rat 2 2 :=
  @matrix.matrix_of_fun rat.rat 2 2 matrix.matrix_key (fun row column =>
    if Nat.eqb (fintype.nat_of_ord row) 0 then
      rational_phase_sign (if Nat.eqb (fintype.nat_of_ord column) 0 then first else second)
    else rational_phase_sign (if Nat.eqb (fintype.nat_of_ord column) 0 then third else fourth)).

Theorem matrix_rank_witness_sound (scalar : divalg.GRing.Field.Exports.fieldType) rows columns rank
  (operator : matrix.matrix scalar rows columns) (upper_left : matrix.matrix scalar rows rank)
  (upper_right : matrix.matrix scalar rank columns) (lower_left : matrix.matrix scalar rank rows)
  (lower_right : matrix.matrix scalar columns rank) :
  operator = matrix.mulmx upper_left upper_right ->
  matrix.mulmx (matrix.mulmx lower_left operator) lower_right = matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar) ->
  mxalgebra.mxrank operator = rank.
Proof.
  move=> factorization lower. apply Nat.le_antisymm.
  - apply (ssrbool.elimT (@ssrnat.leP _ _)). rw factorization. exact: mxalgebra.mulmx_max_rank.
  - apply (ssrbool.elimT (@ssrnat.leP _ _)). exact: mxalgebra.mulmx1_min_rank lower.
Qed.
Definition rational_literal_matrix rows columns (entries : list (list rat.rat)) : matrix.matrix rat.rat rows columns :=
  @matrix.matrix_of_fun rat.rat rows columns matrix.matrix_key (fun row column =>
    List.nth (fintype.nat_of_ord column) (List.nth (fintype.nat_of_ord row) entries nil) rat.zeroq).
Section ReindexTransport.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Lemma reindex_factorization rows columns mapped_rows mapped_columns
  (operator : matrix.matrix scalar rows columns)
  (row_map : fintype.ordinal mapped_rows -> fintype.ordinal rows)
  (column_map : fintype.ordinal mapped_columns -> fintype.ordinal columns) :
  matrix.mxsub row_map column_map operator = matrix.mulmx
    (matrix.mulmx (matrix.rowsub row_map (matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar))) operator)
    (matrix.colsub column_map (matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar))).
Proof.
  pose proof (matrix.mxsub_mul row_map column_map operator
    (matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar))) as factorization.
  rw matrix.mulmx1 matrix.rowsubE in factorization. exact factorization.
Qed.
Lemma reindex_rank_bound rows columns mapped_rows mapped_columns
  (operator : matrix.matrix scalar rows columns)
  (row_map : fintype.ordinal mapped_rows -> fintype.ordinal rows)
  (column_map : fintype.ordinal mapped_columns -> fintype.ordinal columns) :
  mxalgebra.mxrank (matrix.mxsub row_map column_map operator) <= mxalgebra.mxrank operator.
Proof. rw reindex_factorization. apply rank_sandwich_bound. Qed.
Theorem complete_reindex_rank rows columns mapped_rows mapped_columns
  (operator : matrix.matrix scalar rows columns)
  (row_map : fintype.ordinal mapped_rows -> fintype.ordinal rows)
  (column_map : fintype.ordinal mapped_columns -> fintype.ordinal columns)
  (row_back : fintype.ordinal rows -> fintype.ordinal mapped_rows)
  (column_back : fintype.ordinal columns -> fintype.ordinal mapped_columns) :
  (forall row, row_map (row_back row) = row) ->
  (forall column, column_map (column_back column) = column) ->
  mxalgebra.mxrank (matrix.mxsub row_map column_map operator) = mxalgebra.mxrank operator.
Proof.
  move=> rows_complete columns_complete. apply Nat.le_antisymm; [apply reindex_rank_bound|].
  assert (recovered : matrix.mxsub row_back column_back (matrix.mxsub row_map column_map operator) = operator).
  { apply (proj1 (matrix.matrixP _ _)). intros row column. rw !matrix.mxE rows_complete columns_complete. reflexivity. }
  rw -{1}recovered. apply reindex_rank_bound.
Qed.
End ReindexTransport.
Print Assumptions complete_reindex_rank.
