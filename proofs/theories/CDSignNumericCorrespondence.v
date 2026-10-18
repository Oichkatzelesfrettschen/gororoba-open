(** Numeric indices use the last cube component as the highest doubling bit.
    Power-of-two dimensions and sufficient fuel delimit the correspondence. *)
From Stdlib Require Import Arith Bool Lia ZArith.
From OpenGororoba Require Import M3IsAssociator CDSignHalfStep SchreierSignCode CDAssociatorDoubling.
Local Open Scope nat_scope.
Fixpoint cube_encode order : cube order -> nat :=
  match order with O => fun _ => 0 | S lower => fun value =>
    cube_encode lower (fst value) + if snd value then 2 ^ lower else 0 end.
Fixpoint cube_decode order : nat -> cube order :=
  match order with O => fun _ => tt | S lower => fun value =>
    if value <? 2 ^ lower then (cube_decode lower value, false)
    else (cube_decode lower (value - 2 ^ lower), true) end.
Lemma cube_encode_bound : forall order (value : cube order), cube_encode order value < 2 ^ order.
Proof.
  induction order; intros value; [simpl; lia|]. destruct value as [value high].
  specialize (IHorder value). cbn [cube_encode fst snd]. destruct high; simpl; lia.
Qed.
Lemma cube_decode_encode : forall order (value : cube order),
  cube_decode order (cube_encode order value) = value.
Proof.
  induction order; intros value; [destruct value; reflexivity|].
  destruct value as [value high]. pose proof (cube_encode_bound order value).
  cbn [cube_encode cube_decode fst snd]. destruct high.
  - assert (upper : (cube_encode order value + 2 ^ order <? 2 ^ order) = false)
      by (apply Nat.ltb_ge; lia).
    rewrite upper. replace (cube_encode order value + 2 ^ order - 2 ^ order) with
      (cube_encode order value) by lia. rewrite IHorder. reflexivity.
  - rewrite Nat.add_0_r. assert (lower : (cube_encode order value <? 2 ^ order) = true)
      by (apply Nat.ltb_lt; assumption). rewrite lower, IHorder. reflexivity.
Qed.
Lemma cube_encode_decode : forall order value, value < 2 ^ order ->
  cube_encode order (cube_decode order value) = value.
Proof.
  induction order; intros value bounded; [simpl in *; lia|].
  cbn [cube_decode]. destruct (value <? 2 ^ order) eqn:half.
  - apply Nat.ltb_lt in half. cbn [cube_encode fst snd]. rewrite IHorder by assumption. lia.
  - apply Nat.ltb_ge in half. cbn [cube_encode fst snd].
    rewrite IHorder; [lia|]. simpl in bounded. lia.
Qed.
Lemma cube_encode_injective : forall order (left right : cube order),
  cube_encode order left = cube_encode order right -> left = right.
Proof.
  intros order left right equal. rewrite <- (cube_decode_encode order left),
    <- (cube_decode_encode order right). now rewrite equal.
Qed.
Lemma cube_encode_zero : forall order, cube_encode order (cube_zero order) = 0.
Proof. induction order; simpl; [reflexivity|]. rewrite IHorder. reflexivity. Qed.
Lemma cube_encode_zero_iff : forall order (value : cube order),
  cube_encode order value = 0 <-> value = cube_zero order.
Proof.
  intros. rewrite <- (cube_encode_zero order). split.
  - apply cube_encode_injective.
  - intros ->. reflexivity.
Qed.
Lemma cube_encode_nonzero : forall order (value : cube order),
  negb (Nat.eqb (cube_encode order value) 0) = cube_nonzero order value.
Proof.
  intros. unfold cube_nonzero. f_equal.
  destruct (Nat.eqb (cube_encode order value) 0) eqn:numeric;
    destruct (cube_equal order value (cube_zero order)) eqn:recursive; try reflexivity.
  - apply Nat.eqb_eq, cube_encode_zero_iff in numeric. subst.
    rewrite cube_equal_reflexive in recursive. discriminate.
  - apply cube_equal_spec in recursive. subst. rewrite cube_encode_zero, Nat.eqb_refl in numeric.
    discriminate.
Qed.
Lemma bounded_land_high_zero : forall order value, value < 2 ^ order ->
  Nat.land value (2 ^ order) = 0.
Proof.
  intros order value bounded. apply Nat.bits_inj. intro bit.
  rewrite Nat.land_spec, Nat.bits_0. destruct (Nat.eq_dec order bit) as [equal|different].
  - subst bit. rewrite Nat.pow2_bits_true.
    destruct (Nat.eq_dec value 0) as [->|positive].
    + rewrite Nat.bits_0. reflexivity.
    + rewrite Nat.bits_above_log2; [reflexivity|]. apply Nat.log2_lt_pow2; lia.
  - rewrite Nat.pow2_bits_false by assumption. apply andb_false_r.
Qed.
Lemma cube_encode_high_xor : forall order (value : cube order) high,
  cube_encode (S order) (value, high) =
  Nat.lxor (cube_encode order value) (if high then 2 ^ order else 0).
Proof.
  intros. cbn [cube_encode fst snd]. destruct high.
  - apply Nat.add_nocarry_lxor, bounded_land_high_zero, cube_encode_bound.
  - rewrite Nat.lxor_0_r. lia.
Qed.
Theorem cube_encode_xor : forall order (left right : cube order),
  cube_encode order (cube_xor order left right) = Nat.lxor (cube_encode order left) (cube_encode order right).
Proof.
  induction order; intros left right; [reflexivity|].
  destruct left as [left low], right as [right high]. cbn [cube_xor fst snd].
  rewrite !cube_encode_high_xor, IHorder. destruct low, high; simpl;
    rewrite ?Nat.lxor_0_r; repeat rewrite Nat.lxor_assoc; try reflexivity.
  - rewrite <- (Nat.lxor_assoc (2 ^ order) (cube_encode order right) (2 ^ order)),
      (Nat.lxor_comm (2 ^ order) (cube_encode order right)), Nat.lxor_assoc,
      Nat.lxor_nilpotent, Nat.lxor_0_r. reflexivity.
  - rewrite (Nat.lxor_comm (2 ^ order) (cube_encode order right)). reflexivity.
Qed.
Lemma sign_diagonal : forall order (value : cube order),
  sign_exponent order value value = cube_nonzero order value.
Proof.
  induction order; intros value; [reflexivity|]. destruct value as [value high].
  cbn [sign_exponent fst snd]. rewrite IHorder, cube_nonzero_double.
  destruct high, (cube_nonzero order value); reflexivity.
Qed.
Lemma power_half : forall order, (2 ^ S order) / 2 = 2 ^ order.
Proof.
  intros. change ((2 ^ order + (2 ^ order + 0)) / 2 = 2 ^ order).
  replace (2 ^ order + (2 ^ order + 0)) with (2 ^ order * 2) by lia.
  apply Nat.div_mul. lia.
Qed.
Theorem numeric_cube_sign : forall order fuel (left right : cube order), order <= fuel ->
  M3IsAssociator.cd_sign_fuel fuel (2 ^ order) (cube_encode order left) (cube_encode order right) =
  phase_sign (sign_exponent order left right).
Proof.
  induction order; intros fuel left right enough.
  - destruct fuel; reflexivity.
  - destruct fuel as [|fuel]; [lia|]. destruct left as [left low], right as [right high].
    pose proof (cube_encode_bound order left) as left_bound.
    pose proof (cube_encode_bound order right) as right_bound.
    assert (positive : 0 < 2 ^ order) by (pose proof (Nat.pow_nonzero 2 order); lia).
    cbn [cube_encode fst snd]. destruct low, high.
    + rewrite cd_sign_fuel_hi_hi; rewrite ?power_half; try lia.
      replace (cube_encode order right + 2 ^ order - 2 ^ order) with (cube_encode order right) by lia.
      replace (cube_encode order left + 2 ^ order - 2 ^ order) with (cube_encode order left) by lia.
      pose proof (cube_encode_nonzero order right) as right_zero.
      destruct (Nat.eqb (cube_encode order right) 0) eqn:zero.
      * apply Nat.eqb_eq, cube_encode_zero_iff in zero. subst right.
        cbn [sign_exponent fst snd].
        rewrite (proj1 (sign_zero_left order left)), cube_nonzero_zero. reflexivity.
      * rewrite IHorder by lia. cbn [sign_exponent fst snd].
        assert (nonzero : cube_nonzero order right = true) by (rewrite <- right_zero; reflexivity).
        rewrite nonzero. destruct (sign_exponent order right left); reflexivity.
    + rewrite Nat.add_0_r. rewrite cd_sign_fuel_hi_lo; rewrite ?power_half; try lia.
      replace (cube_encode order left + 2 ^ order - 2 ^ order) with (cube_encode order left) by lia.
      rewrite IHorder by lia. cbn [sign_exponent fst snd]. rewrite <- cube_encode_nonzero.
      destruct (Nat.eqb (cube_encode order right) 0), (sign_exponent order left right); reflexivity.
    + rewrite Nat.add_0_r. rewrite cd_sign_fuel_lo_hi; rewrite ?power_half; try lia.
      replace (cube_encode order right + 2 ^ order - 2 ^ order) with (cube_encode order right) by lia.
      rewrite IHorder by lia. cbn [sign_exponent fst snd].
      destruct (sign_exponent order right left); reflexivity.
    + rewrite !Nat.add_0_r. rewrite cd_sign_fuel_lo_lo; rewrite ?power_half; try lia.
      rewrite IHorder by lia. cbn [sign_exponent fst snd].
      destruct (sign_exponent order left right); reflexivity.
Qed.
Theorem numeric_sign_fuel_irrelevant : forall order first second left right,
  order <= first -> order <= second -> left < 2 ^ order -> right < 2 ^ order ->
  M3IsAssociator.cd_sign_fuel first (2 ^ order) left right =
  M3IsAssociator.cd_sign_fuel second (2 ^ order) left right.
Proof.
  intros order first second left right first_enough second_enough left_bound right_bound.
  rewrite <- (cube_encode_decode order left left_bound), <- (cube_encode_decode order right right_bound).
  rewrite !numeric_cube_sign by assumption. reflexivity.
Qed.
Definition numeric_associator_sign order fuel left middle right :=
  (M3IsAssociator.cd_sign_fuel fuel (2 ^ order) middle right *
   M3IsAssociator.cd_sign_fuel fuel (2 ^ order) left (Nat.lxor middle right) *
   M3IsAssociator.cd_sign_fuel fuel (2 ^ order) (Nat.lxor left middle) right *
   M3IsAssociator.cd_sign_fuel fuel (2 ^ order) left middle)%Z.
Theorem numeric_cube_associator : forall order fuel (left middle right : cube order), order <= fuel ->
  numeric_associator_sign order fuel (cube_encode order left) (cube_encode order middle) (cube_encode order right) =
  phase_sign (associator_phase order left middle right).
Proof.
  intros. unfold numeric_associator_sign. rewrite <- !cube_encode_xor.
  rewrite !numeric_cube_sign by assumption.
  unfold associator_phase, schreier. rewrite !phase_sign_xor. ring.
Qed.
Print Assumptions cube_decode_encode.
Print Assumptions cube_encode_decode.
Print Assumptions cube_encode_xor.
Print Assumptions numeric_cube_sign.
Print Assumptions numeric_sign_fuel_irrelevant.
Print Assumptions numeric_cube_associator.

(** Boundary witnesses reject changes to order, argument order and fuel. *)
Example insufficient_fuel_changes_sign :
  M3IsAssociator.cd_sign_fuel 0 4 1 1 <> M3IsAssociator.cd_sign_fuel 2 4 1 1.
Proof. vm_compute. discriminate. Qed.
Example sign_arguments_do_not_commute :
  M3IsAssociator.cd_sign_fuel 2 4 1 2 <> M3IsAssociator.cd_sign_fuel 2 4 2 1.
Proof. vm_compute. discriminate. Qed.
Example highest_bit_encoding : cube_encode 3 (((tt, true), false), true) = 5.
Proof. reflexivity. Qed.
Example high_high_zero_branch : M3IsAssociator.cd_sign_fuel 3 8 5 4 = (-1)%Z.
Proof. reflexivity. Qed.
