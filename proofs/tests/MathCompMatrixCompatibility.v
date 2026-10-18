(** Qualified APIs avoid importing legacy notation and coercion aliases. *)
From Stdlib Require Import Arith.
From mathcomp Require boot order algebra.
Import ssreflect divalg matrix mxalgebra rat.
Set Implicit Arguments.
Section RankWitness.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Variables rows columns rank : nat.
Variable matrix_value : matrix.matrix scalar rows columns.
Variable upper_left : matrix.matrix scalar rows rank.
Variable upper_right : matrix.matrix scalar rank columns.
Variable lower_left : matrix.matrix scalar rank rows.
Variable lower_right : matrix.matrix scalar columns rank.
Theorem matching_rank_witnesses :
  matrix_value = matrix.mulmx upper_left upper_right ->
  matrix.mulmx (matrix.mulmx lower_left matrix_value) lower_right =
    matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar) ->
  mxalgebra.mxrank matrix_value = rank.
Proof.
  move=> factorization lower.
  apply Nat.le_antisymm.
  - apply (ssrbool.elimT (@ssrnat.leP (mxalgebra.mxrank matrix_value) rank)).
    rw factorization. exact: mxalgebra.mulmx_max_rank.
  - apply (ssrbool.elimT (@ssrnat.leP rank (mxalgebra.mxrank matrix_value))). exact: mxalgebra.mulmx1_min_rank lower.
Qed.
End RankWitness.
Print Assumptions matching_rank_witnesses.
Example rational_transpose_roundtrip (value : matrix.matrix rat.rat 2 3) :
  matrix.trmx (matrix.trmx value) = value.
Proof. exact: matrix.trmxK. Qed.
Print Assumptions rational_transpose_roundtrip.
