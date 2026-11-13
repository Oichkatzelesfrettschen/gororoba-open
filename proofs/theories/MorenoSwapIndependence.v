(** Independence of the zero-product swap from the CDAlgMoreno laws.

    The real 3 x 3 matrices, with the matrix product, the transpose as
    conjugation and the Frobenius form as inner product, satisfy every law
    of C1539_MorSkewSymm.CDAlgMoreno: <X Y, Z> = <Y, X^T Z> and
    <X Y, Z> = <X, Z Y^T> are the cyclic invariance of the trace.  The
    skew-symmetric matrix X = E_12 - E_21 is purely imaginary in the sense
    of the interface (conj X = neg X) and has X E_31 = 0 with
    E_31 X = E_32, and E_13 X = 0 with X E_13 = -E_23.  Neither field of
    CDAlgMorenoSwap therefore follows from CDAlgMoreno, and the containment
    of Im(L_x)^perp in Im(R_x)^perp fails with them
    (moreno_laws_leave_image_perp_containment_open), so the kernel equality
    Ker(L_x) = Ker(R_x) is an obligation that a model discharges
    (CDTowerKernelSwap.tower_kernel_swap for the recursive real tower). *)

From Stdlib Require Import Reals Lra.
From OpenGororoba Require Import C1539_MorSkewSymm.
Local Open Scope R_scope.

Record matrix3 : Type := Matrix3 {
  entry11 : R; entry12 : R; entry13 : R;
  entry21 : R; entry22 : R; entry23 : R;
  entry31 : R; entry32 : R; entry33 : R }.

Definition matrix3_zero : matrix3 := Matrix3 0 0 0 0 0 0 0 0 0.

Definition matrix3_neg (value : matrix3) : matrix3 :=
  Matrix3 (- entry11 value) (- entry12 value) (- entry13 value)
          (- entry21 value) (- entry22 value) (- entry23 value)
          (- entry31 value) (- entry32 value) (- entry33 value).

Definition matrix3_transpose (value : matrix3) : matrix3 :=
  Matrix3 (entry11 value) (entry21 value) (entry31 value)
          (entry12 value) (entry22 value) (entry32 value)
          (entry13 value) (entry23 value) (entry33 value).

Definition matrix3_mul (left right : matrix3) : matrix3 :=
  Matrix3
    (entry11 left * entry11 right + entry12 left * entry21 right + entry13 left * entry31 right)
    (entry11 left * entry12 right + entry12 left * entry22 right + entry13 left * entry32 right)
    (entry11 left * entry13 right + entry12 left * entry23 right + entry13 left * entry33 right)
    (entry21 left * entry11 right + entry22 left * entry21 right + entry23 left * entry31 right)
    (entry21 left * entry12 right + entry22 left * entry22 right + entry23 left * entry32 right)
    (entry21 left * entry13 right + entry22 left * entry23 right + entry23 left * entry33 right)
    (entry31 left * entry11 right + entry32 left * entry21 right + entry33 left * entry31 right)
    (entry31 left * entry12 right + entry32 left * entry22 right + entry33 left * entry32 right)
    (entry31 left * entry13 right + entry32 left * entry23 right + entry33 left * entry33 right).

Definition matrix3_inner (left right : matrix3) : R :=
  entry11 left * entry11 right + entry12 left * entry12 right + entry13 left * entry13 right +
  entry21 left * entry21 right + entry22 left * entry22 right + entry23 left * entry23 right +
  entry31 left * entry31 right + entry32 left * entry32 right + entry33 left * entry33 right.

Ltac matrix3_entries :=
  unfold matrix3_inner, matrix3_mul, matrix3_transpose, matrix3_neg, matrix3_zero; cbn.

Module Matrix3Moreno <: CDAlgMoreno.
  Definition A     := matrix3.
  Definition mul   := matrix3_mul.
  Definition conj  := matrix3_transpose.
  Definition neg   := matrix3_neg.
  Definition inner := matrix3_inner.
  Definition zero  := matrix3_zero.

  Lemma inner_adj_left : forall x y z,
    inner (mul x y) z = inner y (mul (conj x) z).
  Proof. intros [] [] []. unfold inner, mul, conj. matrix3_entries. ring. Qed.

  Lemma inner_adj_right : forall x y z,
    inner (mul x y) z = inner x (mul z (conj y)).
  Proof. intros [] [] []. unfold inner, mul, conj. matrix3_entries. ring. Qed.

  Lemma inner_symm : forall x y, inner x y = inner y x.
  Proof. intros [] []. unfold inner, neg. matrix3_entries. ring. Qed.

  Lemma inner_neg_left : forall x y, inner (neg x) y = - inner x y.
  Proof. intros [] []. unfold inner, neg. matrix3_entries. ring. Qed.

  Lemma inner_neg_right : forall x y, inner x (neg y) = - inner x y.
  Proof. intros [] []. unfold inner, neg. matrix3_entries. ring. Qed.

  Lemma inner_zero_left : forall y, inner zero y = 0.
  Proof. intros []. unfold inner, zero. matrix3_entries. ring. Qed.

  Lemma neg_mul_left : forall x y, mul (neg x) y = neg (mul x y).
  Proof. intros [] []. unfold mul, neg. matrix3_entries. f_equal; ring. Qed.

  Lemma neg_mul_right : forall x y, mul x (neg y) = neg (mul x y).
  Proof. intros [] []. unfold mul, neg. matrix3_entries. f_equal; ring. Qed.

  Lemma neg_zero : neg zero = zero.
  Proof. unfold neg, zero. matrix3_entries. f_equal; ring. Qed.

  Lemma inner_nondeg : forall x, (forall y, inner x y = 0) -> x = zero.
  Proof.
    intros [] orthogonal.
    pose proof (orthogonal (Matrix3 1 0 0 0 0 0 0 0 0)) as at11.
    pose proof (orthogonal (Matrix3 0 1 0 0 0 0 0 0 0)) as at12.
    pose proof (orthogonal (Matrix3 0 0 1 0 0 0 0 0 0)) as at13.
    pose proof (orthogonal (Matrix3 0 0 0 1 0 0 0 0 0)) as at21.
    pose proof (orthogonal (Matrix3 0 0 0 0 1 0 0 0 0)) as at22.
    pose proof (orthogonal (Matrix3 0 0 0 0 0 1 0 0 0)) as at23.
    pose proof (orthogonal (Matrix3 0 0 0 0 0 0 1 0 0)) as at31.
    pose proof (orthogonal (Matrix3 0 0 0 0 0 0 0 1 0)) as at32.
    pose proof (orthogonal (Matrix3 0 0 0 0 0 0 0 0 1)) as at33.
    unfold inner, matrix3_inner in *. cbn in *. unfold zero, matrix3_zero. f_equal; lra.
  Qed.
End Matrix3Moreno.

(** X = E_12 - E_21, and the two vectors it annihilates on one side only. *)
Definition skew_operand : matrix3 := Matrix3 0 1 0 (-1) 0 0 0 0 0.
Definition left_annihilated : matrix3 := Matrix3 0 0 0 0 0 0 1 0 0.
Definition right_annihilated : matrix3 := Matrix3 0 0 1 0 0 0 0 0 0.

Lemma skew_operand_pure : matrix3_transpose skew_operand = matrix3_neg skew_operand.
Proof. matrix3_entries. f_equal; ring. Qed.

Theorem matrix3_left_swap_fails :
  matrix3_mul skew_operand left_annihilated = matrix3_zero /\
  matrix3_mul left_annihilated skew_operand <> matrix3_zero.
Proof.
  split.
  - unfold skew_operand, left_annihilated, right_annihilated. matrix3_entries. f_equal; ring.
  - intro vanishing. apply (f_equal entry32) in vanishing.
    unfold skew_operand, left_annihilated, matrix3_mul, matrix3_zero in vanishing. cbn in vanishing. lra.
Qed.

Theorem matrix3_right_swap_fails :
  matrix3_mul right_annihilated skew_operand = matrix3_zero /\
  matrix3_mul skew_operand right_annihilated <> matrix3_zero.
Proof.
  split.
  - unfold skew_operand, left_annihilated, right_annihilated. matrix3_entries. f_equal; ring.
  - intro vanishing. apply (f_equal entry23) in vanishing.
    unfold skew_operand, right_annihilated, matrix3_mul, matrix3_zero in vanishing. cbn in vanishing. lra.
Qed.

(** Neither obligation of CDAlgMorenoSwap holds in the model Matrix3Moreno. *)
Theorem moreno_laws_leave_left_swap_open :
  ~ (forall x y : Matrix3Moreno.A,
      Matrix3Moreno.conj x = Matrix3Moreno.neg x ->
      Matrix3Moreno.mul x y = Matrix3Moreno.zero ->
      Matrix3Moreno.mul y x = Matrix3Moreno.zero).
Proof.
  intro swap. destruct matrix3_left_swap_fails as [vanishing nonzero].
  exact (nonzero (swap skew_operand left_annihilated skew_operand_pure vanishing)).
Qed.

Theorem moreno_laws_leave_right_swap_open :
  ~ (forall x y : Matrix3Moreno.A,
      Matrix3Moreno.conj x = Matrix3Moreno.neg x ->
      Matrix3Moreno.mul y x = Matrix3Moreno.zero ->
      Matrix3Moreno.mul x y = Matrix3Moreno.zero).
Proof.
  intro swap. destruct matrix3_right_swap_fails as [vanishing nonzero].
  exact (nonzero (swap skew_operand right_annihilated skew_operand_pure vanishing)).
Qed.

(** Statement (f) of C1539_MorSkewSymm.v, Im(L_x)^perp inside Im(R_x)^perp
    for purely imaginary x, fails in the same model: E_31 is orthogonal to
    Im(L_X) because X E_31 = 0, and orthogonality to Im(R_X) would give
    E_31 X = 0. *)
Module Matrix3Skew := MorSkewSymm Matrix3Moreno.

Theorem moreno_laws_leave_image_perp_containment_open :
  ~ (forall x y : Matrix3Moreno.A,
      Matrix3Moreno.conj x = Matrix3Moreno.neg x ->
      (forall z, Matrix3Moreno.inner y (Matrix3Moreno.mul x z) = 0) ->
      (forall z, Matrix3Moreno.inner y (Matrix3Moreno.mul z x) = 0)).
Proof.
  intro containment. destruct matrix3_left_swap_fails as [vanishing nonzero].
  apply nonzero.
  apply (Matrix3Skew.perp_im_rx_implies_yx_zero skew_operand left_annihilated skew_operand_pure).
  apply (containment skew_operand left_annihilated skew_operand_pure).
  exact (Matrix3Skew.lx_zero_implies_perp skew_operand left_annihilated skew_operand_pure vanishing).
Qed.

Print Assumptions moreno_laws_leave_left_swap_open.
Print Assumptions moreno_laws_leave_right_swap_open.
Print Assumptions moreno_laws_leave_image_perp_containment_open.
