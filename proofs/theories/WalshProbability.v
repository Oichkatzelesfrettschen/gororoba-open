(** Integer Walsh identities precede real normalization and physical use. *)
From Stdlib Require Import Arith ZArith ZArithRing Bool Lia btauto.Btauto.
From OpenGororoba Require Import SchreierSignCode CDAssociatorDoubling.
Local Open Scope Z_scope.
Lemma integer_cube_sum_add : forall order first second,
  integer_cube_sum order (fun input => first input + second input) =
  integer_cube_sum order first + integer_cube_sum order second.
Proof. induction order; intros; simpl; [reflexivity|]. rewrite !IHorder. ring. Qed.
Lemma integer_cube_sum_constant : forall order value,
  integer_cube_sum order (fun _ => value) = Z.of_nat (Nat.pow 2 order) * value.
Proof.
  induction order; intros; [change (value = 1 * value); ring|].
  cbn [integer_cube_sum]. rewrite !IHorder, Nat.pow_succ_r', Nat2Z.inj_mul. cbn [Z.of_nat]. ring.
Qed.
Lemma walsh_slices : forall order function frequency high,
  walsh (S order) function (frequency, high) =
  walsh order (fun input => function (input, false)) frequency +
  phase_sign high * walsh order (fun input => function (input, true)) frequency.
Proof.
  intros. unfold walsh. cbn [integer_cube_sum cube_dot fst snd].
  f_equal.
  - apply integer_cube_sum_ext. intros. f_equal. btauto.
  - rewrite <- integer_cube_sum_scale. apply integer_cube_sum_ext. intros.
    rewrite <- phase_sign_xor. f_equal. btauto.
Qed.
Theorem walsh_parseval_integer : forall order function,
  integer_cube_sum order (fun frequency => walsh order function frequency ^ 2) =
  Z.of_nat (Nat.pow 2 order) ^ 2.
Proof.
  induction order; intros function.
  - change (phase_sign (xorb (function tt) false) ^ 2 = 1).
    destruct (function tt); reflexivity.
  - cbn [integer_cube_sum].
    transitivity (integer_cube_sum order (fun frequency =>
      2 * (walsh order (fun input => function (input, false)) frequency ^ 2 +
           walsh order (fun input => function (input, true)) frequency ^ 2))).
    + rewrite <- integer_cube_sum_add. apply integer_cube_sum_ext. intro frequency.
      rewrite !walsh_slices. cbn [phase_sign]. ring.
    + rewrite integer_cube_sum_scale, integer_cube_sum_add, !IHorder,
        Nat.pow_succ_r', Nat2Z.inj_mul. cbn [Z.of_nat]. ring.
Qed.
Lemma cube_dot_xor : forall order (left right input : cube order),
  cube_dot order (cube_xor order left right) input =
  xorb (cube_dot order left input) (cube_dot order right input).
Proof.
  induction order; intros; [reflexivity|]. destruct left as [left low], right as [right high], input as [input bit].
  cbn [cube_dot cube_xor fst snd]. rewrite IHorder. btauto.
Qed.
Lemma cube_dot_zero : forall order input, cube_dot order (cube_zero order) input = false.
Proof.
  induction order; intros; [reflexivity|]. destruct input as [input high].
  cbn [cube_dot cube_zero fst snd]. rewrite IHorder. reflexivity.
Qed.
Theorem walsh_character_sum : forall order (frequency : cube order),
  integer_cube_sum order (fun input => phase_sign (cube_dot order frequency input)) =
  if cube_equal order frequency (cube_zero order) then Z.of_nat (Nat.pow 2 order) else 0.
Proof.
  induction order; intros frequency; [reflexivity|]. destruct frequency as [frequency high].
  cbn [integer_cube_sum cube_dot cube_equal cube_zero fst snd].
  transitivity (integer_cube_sum order (fun input => phase_sign (cube_dot order frequency input)) +
    phase_sign high * integer_cube_sum order (fun input => phase_sign (cube_dot order frequency input))).
  - f_equal.
    + apply integer_cube_sum_ext. intro input. f_equal. btauto.
    + rewrite <- integer_cube_sum_scale. apply integer_cube_sum_ext. intro input.
      rewrite <- phase_sign_xor. f_equal. btauto.
  - rewrite IHorder. destruct high, (cube_equal order frequency (cube_zero order));
      cbn [Bool.eqb andb phase_sign]; rewrite ?Nat.pow_succ_r', ?Nat2Z.inj_mul; cbn [Z.of_nat]; ring.
Qed.
Theorem walsh_character_orthogonality : forall order (left right : cube order),
  integer_cube_sum order (fun input => phase_sign (cube_dot order left input) * phase_sign (cube_dot order right input)) =
  if cube_equal order left right then Z.of_nat (Nat.pow 2 order) else 0.
Proof.
  intros. transitivity (integer_cube_sum order (fun input => phase_sign (cube_dot order (cube_xor order left right) input))).
  - apply integer_cube_sum_ext. intro input. rewrite cube_dot_xor, phase_sign_xor. reflexivity.
  - rewrite walsh_character_sum, cube_equal_translate, cube_xor_zero, cube_equal_symmetric. reflexivity.
Qed.
Print Assumptions walsh_parseval_integer.
Print Assumptions walsh_character_orthogonality.

From Stdlib Require Import Reals List Lra Psatz.
From OpenGororoba Require Import FiniteProbability.
Import ListNotations.
Local Open Scope R_scope.
Fixpoint real_cube_sum order : (cube order -> R) -> R :=
  match order with O => fun function => function tt | S lower => fun function =>
    real_cube_sum lower (fun input => function (input, false)) +
    real_cube_sum lower (fun input => function (input, true)) end.
Lemma real_cube_sum_ext : forall order first second,
  (forall input, first input = second input) -> real_cube_sum order first = real_cube_sum order second.
Proof.
  induction order; intros first second equal; simpl; [apply equal|].
  rewrite (IHorder _ _ (fun input => equal (input, false))),
    (IHorder _ _ (fun input => equal (input, true))). reflexivity.
Qed.
Lemma real_cube_sum_scale : forall order factor function,
  real_cube_sum order (fun input => factor * function input) = factor * real_cube_sum order function.
Proof. induction order; intros; simpl; [reflexivity|]. rewrite !IHorder. ring. Qed.
Lemma real_cube_sum_IZR : forall order function,
  real_cube_sum order (fun input => IZR (function input)) = IZR (integer_cube_sum order function).
Proof. induction order; intros; simpl; [reflexivity|]. rewrite !IHorder, plus_IZR. reflexivity. Qed.
Lemma IZR_square : forall value, IZR (value ^ 2) = IZR value ^ 2.
Proof. intros. replace (value ^ 2)%Z with (value * value)%Z by ring. rewrite mult_IZR. ring. Qed.
Definition walsh_probability order function frequency :=
  IZR (walsh order function frequency) ^ 2 / INR (Nat.pow 2 order) ^ 2.
Lemma cube_cardinality_positive : forall order, 0 < INR (Nat.pow 2 order).
Proof. intro. apply lt_0_INR. pose proof (Nat.pow_nonzero 2 order). lia. Qed.
Theorem walsh_probability_nonnegative : forall order function frequency,
  0 <= walsh_probability order function frequency.
Proof. intros. unfold walsh_probability, Rdiv. apply Rmult_le_pos; [apply pow2_ge_0|].
  apply Rlt_le, Rinv_0_lt_compat.
  pose proof (cube_cardinality_positive order). nra. Qed.
Theorem walsh_probability_total : forall order function,
  real_cube_sum order (walsh_probability order function) = 1.
Proof.
  intros. unfold walsh_probability.
  transitivity (/ INR (Nat.pow 2 order) ^ 2 *
    real_cube_sum order (fun frequency => IZR (walsh order function frequency ^ 2))).
  - rewrite <- real_cube_sum_scale. apply real_cube_sum_ext. intro frequency.
    rewrite IZR_square. unfold Rdiv. ring.
  - rewrite real_cube_sum_IZR, walsh_parseval_integer, IZR_square, <- INR_IZR_INZ.
    pose proof (cube_cardinality_positive order). field; nra.
Qed.
Fixpoint cube_points order : list (cube order) :=
  match order with O => [tt] | S lower =>
    map (fun input => (input, false)) (cube_points lower) ++
    map (fun input => (input, true)) (cube_points lower) end.
Lemma cube_points_sum : forall order function,
  real_sum (map function (cube_points order)) = real_cube_sum order function.
Proof.
  induction order; intros; [simpl; ring|]. cbn [cube_points real_cube_sum].
  rewrite map_app, !map_map.
  assert (append_sum : forall first second, real_sum (first ++ second) = real_sum first + real_sum second).
  { induction first; intros; simpl; [ring|]. rewrite IHfirst. ring. }
  rewrite append_sum, !IHorder. reflexivity.
Qed.
Definition walsh_law order function : list (cube order * R) :=
  map (fun frequency => (frequency, walsh_probability order function frequency)) (cube_points order).
Theorem walsh_law_nonnegative : forall order function, nonnegative_law (walsh_law order function).
Proof.
  intros. unfold nonnegative_law, walsh_law. apply Forall_forall. intros point member.
  apply in_map_iff in member as [frequency [<- _]]. simpl. apply walsh_probability_nonnegative.
Qed.
Theorem walsh_law_normalized : forall order function, normalized_law (walsh_law order function).
Proof.
  intros. unfold normalized_law, weighted_expectation, walsh_law.
  replace (fold_right (fun point total => snd point * 1 + total) 0
    (map (fun frequency => (frequency, walsh_probability order function frequency)) (cube_points order)))
    with (real_sum (map (walsh_probability order function) (cube_points order))).
  - rewrite cube_points_sum. apply walsh_probability_total.
  - induction (cube_points order) as [|frequency rest IH]; simpl; [reflexivity|]. rewrite <- IH. ring.
Qed.
Theorem walsh_probability_parity_extension : forall order function coefficient frequency high,
  walsh_probability (S order)
    (fun input => xorb (function (fst input)) (andb (snd input) coefficient)) (frequency, high) =
  if Bool.eqb high coefficient then walsh_probability order function frequency else 0.
Proof.
  intros. unfold walsh_probability. rewrite walsh_parity_extension.
  rewrite Nat.pow_succ_r', mult_INR. cbn [INR].
  destruct (Bool.eqb high coefficient).
  - rewrite mult_IZR. cbn [IZR]. pose proof (cube_cardinality_positive order). field; nra.
  - cbn [IZR]. unfold Rdiv. ring.
Qed.
Print Assumptions walsh_law_nonnegative.
Print Assumptions walsh_law_normalized.
Print Assumptions walsh_probability_parity_extension.
