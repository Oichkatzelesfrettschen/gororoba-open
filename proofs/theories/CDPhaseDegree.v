(** Sign-row and associator degree use canonical finite ANF coordinates. *)
From Stdlib Require Import Arith Bool Lia ZArith btauto.Btauto.
From OpenGororoba Require Import SchreierSignCode CDAssociatorDoubling CDSignNumericCorrespondence BooleanANFDegree.
Local Open Scope nat_scope.
Lemma phase_cube_xor_self : forall order (value : cube order), cube_xor order value value = cube_zero order.
Proof.
  induction order; intros value; [destruct value; reflexivity|]. destruct value as [value high].
  cbn [cube_xor cube_zero fst snd]. rewrite IHorder, xorb_nilpotent. reflexivity.
Qed.
Lemma phase_cube_xor_involution : forall order (left right : cube order),
  cube_xor order left (cube_xor order left right) = right.
Proof.
  induction order; intros left right; [destruct left, right; reflexivity|].
  destruct left as [left low], right as [right high]. cbn [cube_xor fst snd].
  rewrite IHorder. destruct low, high; reflexivity.
Qed.
Lemma phase_cube_equal_cancel : forall order (left right : cube order),
  cube_equal order left (cube_xor order left right) = cube_equal order right (cube_zero order).
Proof.
  intros. rewrite cube_equal_symmetric, cube_equal_translate, phase_cube_xor_self. reflexivity.
Qed.
Lemma phase_cube_xor_nonzero : forall order (left right : cube order),
  cube_nonzero order (cube_xor order left right) = negb (cube_equal order left right).
Proof.
  intros. unfold cube_nonzero. rewrite cube_equal_translate, cube_xor_zero, cube_equal_symmetric. reflexivity.
Qed.
Lemma commutation_pair_coefficient : forall order (left right : cube order),
  commutation_phase order left right = pair_coefficient order left right.
Proof.
  intros. unfold commutation_phase, pair_coefficient. rewrite sign_commutator, phase_cube_xor_nonzero. btauto.
Qed.
Theorem sign_row_involution : forall order (left input : cube order),
  xorb (sign_exponent order left input) (sign_exponent order left (cube_xor order left input)) = cube_nonzero order left.
Proof.
  induction order; intros left input; [reflexivity|].
  destruct left as [left low], input as [input high].
  pose proof (IHorder left input) as lower.
  rewrite cube_nonzero_double. cbn [sign_exponent cube_xor fst snd].
  destruct low, high; cbn [xorb andb];
    rewrite ?(sign_transpose order left input),
      ?(sign_transpose order left (cube_xor order left input)),
      ?phase_cube_equal_cancel, ?phase_cube_xor_nonzero;
    unfold cube_nonzero in *;
    rewrite ?(cube_equal_symmetric order input left); try btauto.
  all: destruct (sign_exponent order left input),
    (sign_exponent order left (cube_xor order left input)),
    (cube_equal order left input), (cube_equal order input (cube_zero order)),
    (cube_equal order left (cube_zero order)); simpl in *; congruence.
Qed.
Theorem degenerate_associator_zero : forall order (value input : cube order),
  associator_phase order (cube_zero order) value input = false /\
  associator_phase order value (cube_zero order) input = false /\
  associator_phase order value value input = false.
Proof.
  intros. unfold associator_phase, schreier.
  rewrite (proj1 (sign_zero_left order input)), (proj1 (sign_zero_left order value)),
    (proj2 (sign_zero_left order value)), cube_xor_zero,
    (cube_xor_commutative order (cube_zero order) value), cube_xor_zero,
    (cube_xor_commutative order (cube_zero order) input), cube_xor_zero,
    phase_cube_xor_self, (proj1 (sign_zero_left order input)), sign_diagonal.
  rewrite (proj1 (sign_zero_left order (cube_xor order value input))).
  pose proof (sign_row_involution order value input) as inverse.
  destruct (sign_exponent order value input), (sign_exponent order value (cube_xor order value input)),
    (cube_nonzero order value); simpl in *; repeat split; congruence.
Qed.
Print Assumptions sign_row_involution.
Print Assumptions degenerate_associator_zero.

Lemma phase_nonzero_distinct_zero : forall order (value : cube order),
  cube_nonzero order value = true -> cube_zero order <> value.
Proof. intros order value nonzero equal. subst value. rewrite cube_nonzero_zero in nonzero. discriminate. Qed.
Theorem nonzero_indicator_degree : forall order, 0 < order ->
  anf_degree order (cube_nonzero order) = order.
Proof.
  intros order positive.
  transitivity (anf_degree order (fun input => xorb (cube_equal order input (cube_zero order)) true)).
  - apply anf_degree_ext. intro input. unfold cube_nonzero. destruct (cube_equal order input (cube_zero order)); reflexivity.
  - rewrite anf_degree_add_constant; rewrite point_indicator_degree; auto.
Qed.
Lemma commutation_row_degree : forall order (left : cube order) high, 2 <= order ->
  cube_nonzero order left = true ->
  anf_degree order (fun input => xorb (commutation_phase order left input) high) = order - 1.
Proof.
  intros order left high order_large nonzero.
  pose proof (phase_nonzero_distinct_zero order left nonzero) as different.
  transitivity (anf_degree order (fun input => xorb
    (xorb (cube_equal order input (cube_zero order)) (cube_equal order input left)) (xorb true high))).
  - apply anf_degree_ext. intro input. unfold commutation_phase.
    rewrite sign_commutator, nonzero. unfold cube_nonzero.
    rewrite (cube_equal_symmetric order left input). btauto.
  - rewrite anf_degree_add_constant.
    + apply two_point_indicator_degree. exact different.
    + rewrite two_point_indicator_degree by exact different. lia.
Qed.
Lemma sign_row_append : forall order (left : cube order) high input,
  sign_exponent (S order) (left, high) input =
  append_boolean order
    (fun lower => xorb (sign_exponent order left lower) (andb high (cube_nonzero order lower)))
    (fun lower => xorb (commutation_phase order left lower) high) input.
Proof.
  intros order left high [input bit]. rewrite sign_doubling.
  unfold append_boolean. cbn [fst snd]. btauto.
Qed.
Theorem sign_row_degree : forall extra (left : cube (S (S extra))),
  cube_nonzero (S (S extra)) left = true ->
  anf_degree (S (S extra)) (sign_exponent (S (S extra)) left) = S extra.
Proof.
  induction extra; intros left nonzero.
  - destruct left as [[[] first] second]. destruct first, second;
      vm_compute in *; try discriminate; reflexivity.
  - destruct left as [left high]. rewrite cube_nonzero_double in nonzero.
    destruct (cube_nonzero (S (S extra)) left) eqn:lower_nonzero.
    + assert (comm_degree : anf_degree (S (S extra))
        (fun input => xorb (commutation_phase (S (S extra)) left input) high) = S extra).
      { rewrite commutation_row_degree; auto; lia. }
      transitivity (anf_degree (S (S (S extra)))
        (append_boolean (S (S extra))
          (fun input => xorb (sign_exponent (S (S extra)) left input) (andb high (cube_nonzero (S (S extra)) input)))
          (fun input => xorb (commutation_phase (S (S extra)) left input) high))).
      * apply anf_degree_ext. intro input. apply sign_row_append.
      * rewrite append_boolean_degree.
        2: { apply positive_degree_has_coefficient. rewrite comm_degree. lia. }
        rewrite comm_degree. destruct high.
        -- change (Nat.max (anf_degree (S (S extra)) (fun input => xorb
             (sign_exponent (S (S extra)) left input) (cube_nonzero (S (S extra)) input)))
             (S (S extra)) = S (S extra)).
           rewrite anf_degree_strict_xor.
           ++ rewrite nonzero_indicator_degree by lia. apply Nat.max_id.
           ++ rewrite IHextra by exact lower_nonzero. rewrite nonzero_indicator_degree by lia. lia.
        -- assert (low_degree : anf_degree (S (S extra))
             (fun input => xorb (sign_exponent (S (S extra)) left input) (andb false (cube_nonzero (S (S extra)) input))) = S extra).
           { transitivity (anf_degree (S (S extra)) (sign_exponent (S (S extra)) left)).
             - apply anf_degree_ext. intro input. destruct (sign_exponent (S (S extra)) left input); reflexivity.
             - apply IHextra. exact lower_nonzero. }
           rewrite low_degree. lia.
    + assert (left_zero : left = cube_zero (S (S extra))).
      { unfold cube_nonzero in lower_nonzero. apply negb_false_iff, cube_equal_spec in lower_nonzero. exact lower_nonzero. }
      subst left. destruct high; [|discriminate].
      transitivity (anf_degree (S (S (S extra))) (append_parity (S (S extra)) (cube_nonzero (S (S extra))) true)).
      * apply anf_degree_ext. intros [input bit]. rewrite sign_doubling. unfold commutation_phase.
        rewrite (proj1 (sign_zero_left (S (S extra)) input)), (proj2 (sign_zero_left (S (S extra)) input)).
        unfold append_parity. cbn [fst snd]. destruct bit, (cube_nonzero (S (S extra)) input); reflexivity.
      * rewrite append_parity_degree, nonzero_indicator_degree by lia. simpl. lia.
Qed.
Print Assumptions sign_row_degree.

Lemma commutation_delta : forall order (left input : cube order),
  commutation_phase order left input = xorb (cube_nonzero order left)
    (xorb (cube_equal order input (cube_zero order)) (cube_equal order input left)).
Proof.
  intros. unfold commutation_phase. rewrite sign_commutator.
  unfold cube_nonzero. rewrite (cube_equal_symmetric order left input). btauto.
Qed.
Lemma pair_coefficient_delta : forall order (left input : cube order),
  pair_coefficient order left input = xorb (cube_nonzero order left)
    (xorb (cube_equal order input (cube_zero order)) (cube_equal order input left)).
Proof. intros. rewrite <- commutation_pair_coefficient. apply commutation_delta. Qed.
Lemma shifted_commutation_delta : forall order (left shift input : cube order),
  commutation_phase order left (cube_xor order shift input) = xorb (cube_nonzero order left)
    (xorb (cube_equal order input shift) (cube_equal order input (cube_xor order left shift))).
Proof.
  intros. rewrite commutation_delta, !cube_equal_translate, cube_xor_zero,
    (cube_xor_commutative order shift left). reflexivity.
Qed.
Lemma associator_slice_left : forall order (left middle input : cube order),
  associator_phase (S order) (left, true) (middle, false) (input, false) =
  xorb (associator_phase order left middle input)
    (xorb (xorb (cube_equal order input (cube_zero order)) (cube_equal order input middle))
      (cube_nonzero order middle)).
Proof.
  intros. transitivity (xorb (associator_phase order left middle input) (pair_coefficient order middle input)).
  - rewrite associator_doubling. unfold pair_coefficient. btauto.
  - rewrite pair_coefficient_delta. btauto.
Qed.
Lemma associator_slice_right : forall order (left middle input : cube order),
  associator_phase (S order) (left, false) (middle, true) (input, false) =
  xorb (associator_phase order left middle input)
    (xorb (xorb (cube_equal order input middle) (cube_equal order input (cube_xor order left middle)))
      (xorb (cube_nonzero order left) (commutation_phase order left middle))).
Proof.
  intros. transitivity (xorb (associator_phase order left middle input)
    (xorb (commutation_phase order left middle) (commutation_phase order left (cube_xor order middle input)))).
  - rewrite associator_doubling. btauto.
  - rewrite shifted_commutation_delta. btauto.
Qed.
Lemma associator_slice_both : forall order (left middle input : cube order),
  associator_phase (S order) (left, true) (middle, true) (input, false) =
  xorb (associator_phase order left middle input)
    (xorb (xorb (cube_equal order input (cube_zero order)) (cube_equal order input (cube_xor order left middle)))
      (xorb (cube_nonzero order middle) (xorb (cube_nonzero order left) (commutation_phase order left middle)))).
Proof.
  intros. transitivity (xorb (associator_phase order left middle input)
    (xorb (pair_coefficient order middle input)
      (xorb (commutation_phase order left middle) (commutation_phase order left (cube_xor order middle input))))).
  - rewrite associator_doubling. unfold pair_coefficient. btauto.
  - rewrite shifted_commutation_delta, pair_coefficient_delta. btauto.
Qed.
Lemma associator_as_parity_extension : forall order (left middle : cube order) low high input,
  associator_phase (S order) (left, low) (middle, high) input =
  append_parity order (fun lower => associator_phase (S order) (left, low) (middle, high) (lower, false))
    (pair_coefficient order left middle) input.
Proof.
  intros order left middle low high [input bit].
  pose proof (schreier_high_difference order left middle input low high) as derivative.
  change (xorb (schreier (S order) (left, low) (middle, high) (input, false))
    (schreier (S order) (left, low) (middle, high) (input, true)) = pair_coefficient order left middle) in derivative.
  unfold append_parity. cbn [fst snd]. destruct bit.
  - rewrite <- derivative. unfold associator_phase. btauto.
  - unfold associator_phase. btauto.
Qed.
Theorem quaternion_associator_all : forall left middle input : cube 2,
  associator_phase 2 left middle input = false.
Proof. intros [[[] []] []] [[[] []] []] [[[] []] []]; reflexivity. Qed.
Print Assumptions associator_as_parity_extension.
Print Assumptions quaternion_associator_all.

Lemma two_point_defect_degree : forall order lower (left right : cube order) constant,
  2 <= order -> anf_degree order lower <= order - 2 -> left <> right ->
  anf_degree order (fun input => xorb (lower input)
    (xorb (xorb (cube_equal order input left) (cube_equal order input right)) constant)) = order - 1.
Proof.
  intros order lower left right constant order_bound lower_bound distinct.
  assert (defect_degree : anf_degree order (fun input =>
    xorb (xorb (cube_equal order input left) (cube_equal order input right)) constant) = order - 1).
  { rewrite anf_degree_add_constant.
    - apply two_point_indicator_degree. exact distinct.
    - rewrite two_point_indicator_degree by exact distinct. lia. }
  rewrite anf_degree_strict_xor; [exact defect_degree|rewrite defect_degree; lia].
Qed.
Lemma cube_zero_distinct : forall order (value : cube order),
  cube_nonzero order value = true -> cube_zero order <> value.
Proof.
  intros order value nonzero equal. subst value. unfold cube_nonzero in nonzero.
  rewrite cube_equal_reflexive in nonzero. discriminate.
Qed.
Lemma cube_xor_right_cancel : forall order (left right : cube order),
  cube_xor order (cube_xor order left right) right = left.
Proof. intros. rewrite (cube_xor_commutative order (cube_xor order left right) right), (cube_xor_commutative order left right), phase_cube_xor_involution. reflexivity. Qed.

Theorem associator_step_degree : forall order (left middle : cube order) low high,
  2 <= order ->
  (forall first second : cube order, anf_degree order (associator_phase order first second) <= order - 2) ->
  cube_nonzero (S order) (left, low) = true ->
  cube_nonzero (S order) (middle, high) = true ->
  (left, low) <> (middle, high) ->
  anf_degree (S order) (associator_phase (S order) (left, low) (middle, high)) =
    if orb low high then order - 1
    else Nat.max (anf_degree order (associator_phase order left middle)) 1.
Proof.
  intros order left middle low high order_bound lower_bound left_nonzero middle_nonzero distinct.
  transitivity (anf_degree (S order) (append_parity order
    (fun input => associator_phase (S order) (left, low) (middle, high) (input, false))
    (pair_coefficient order left middle))).
  { apply anf_degree_ext. intro input. apply associator_as_parity_extension. }
  rewrite append_parity_degree. destruct low, high; simpl.
  - assert (different : left <> middle) by (intro equal; apply distinct; now subst).
    assert (xor_distinct : cube_zero order <> cube_xor order left middle).
    { apply cube_zero_distinct. rewrite phase_cube_xor_nonzero.
      apply negb_true_iff. destruct (cube_equal order left middle) eqn:equal; [|reflexivity].
      apply cube_equal_spec in equal. contradiction. }
    assert (slice_degree : anf_degree order (fun input =>
      associator_phase (S order) (left, true) (middle, true) (input, false)) = order - 1).
    { transitivity (anf_degree order (fun input => xorb (associator_phase order left middle input)
        (xorb (xorb (cube_equal order input (cube_zero order)) (cube_equal order input (cube_xor order left middle)))
          (xorb (cube_nonzero order middle) (xorb (cube_nonzero order left) (commutation_phase order left middle)))))).
      - apply anf_degree_ext. intro input. apply associator_slice_both.
      - apply two_point_defect_degree; auto. }
    rewrite slice_degree. destruct (pair_coefficient order left middle); lia.
  - rewrite cube_nonzero_double, orb_false_r in middle_nonzero.
    assert (slice_degree : anf_degree order (fun input =>
      associator_phase (S order) (left, true) (middle, false) (input, false)) = order - 1).
    { transitivity (anf_degree order (fun input => xorb (associator_phase order left middle input)
        (xorb (xorb (cube_equal order input (cube_zero order)) (cube_equal order input middle)) (cube_nonzero order middle)))).
      - apply anf_degree_ext. intro input. apply associator_slice_left.
      - apply two_point_defect_degree; auto using cube_zero_distinct. }
    rewrite slice_degree. destruct (pair_coefficient order left middle); lia.
  - rewrite cube_nonzero_double, orb_false_r in left_nonzero.
    assert (targets_distinct : middle <> cube_xor order left middle).
    { intro equal. apply (cube_zero_distinct order left left_nonzero).
      pose proof (f_equal (fun value => cube_xor order value middle) equal) as cancelled.
      cbn beta in cancelled. rewrite phase_cube_xor_self, cube_xor_right_cancel in cancelled. exact cancelled. }
    assert (slice_degree : anf_degree order (fun input =>
      associator_phase (S order) (left, false) (middle, true) (input, false)) = order - 1).
    { transitivity (anf_degree order (fun input => xorb (associator_phase order left middle input)
        (xorb (xorb (cube_equal order input middle) (cube_equal order input (cube_xor order left middle)))
          (xorb (cube_nonzero order left) (commutation_phase order left middle))))).
      - apply anf_degree_ext. intro input. apply associator_slice_right.
      - apply two_point_defect_degree; auto. }
    rewrite slice_degree. destruct (pair_coefficient order left middle); lia.
  - assert (lower_distinct : left <> middle) by (intro equal; apply distinct; now subst).
    rewrite cube_nonzero_double, orb_false_r in left_nonzero, middle_nonzero.
    assert (coefficient : pair_coefficient order left middle = true).
    { unfold pair_coefficient. rewrite left_nonzero, middle_nonzero, phase_cube_xor_nonzero.
      destruct (cube_equal order left middle) eqn:equal; [|reflexivity].
      apply cube_equal_spec in equal. contradiction. }
    rewrite coefficient. f_equal. apply anf_degree_ext. intro input.
    rewrite associator_doubling. btauto.
Qed.
Print Assumptions associator_step_degree.

Lemma associator_degenerate_degree : forall order (left middle : cube order),
  cube_nonzero order left = false \/ cube_nonzero order middle = false \/ left = middle ->
  anf_degree order (associator_phase order left middle) = 0.
Proof.
  intros order left middle degenerate.
  transitivity (anf_degree order (fun _ => false)); [|apply anf_degree_zero].
  apply anf_degree_ext. intro input. destruct degenerate as [zero|[zero|equal]].
  - unfold cube_nonzero in zero. apply negb_false_iff, cube_equal_spec in zero. subst left.
    apply (proj1 (degenerate_associator_zero order middle input)).
  - unfold cube_nonzero in zero. apply negb_false_iff, cube_equal_spec in zero. subst middle.
    apply (proj1 (proj2 (degenerate_associator_zero order left input))).
  - subst middle. apply (proj2 (proj2 (degenerate_associator_zero order left input))).
Qed.
Theorem associator_degree_bound : forall extra (left middle : cube (S (S extra))),
  anf_degree (S (S extra)) (associator_phase (S (S extra)) left middle) <= extra.
Proof.
  induction extra; intros left middle.
  - assert (zero : anf_degree 2 (associator_phase 2 left middle) = 0).
    { transitivity (anf_degree 2 (fun _ => false)); [|apply anf_degree_zero].
      apply anf_degree_ext. intro input. apply quaternion_associator_all. }
    lia.
  - destruct (cube_nonzero (S (S (S extra))) left) eqn:left_nonzero.
    2: { rewrite associator_degenerate_degree; [lia|auto]. }
    destruct (cube_nonzero (S (S (S extra))) middle) eqn:middle_nonzero.
    2: { rewrite associator_degenerate_degree; [lia|auto]. }
    destruct (cube_equal (S (S (S extra))) left middle) eqn:equal.
    { apply cube_equal_spec in equal. rewrite associator_degenerate_degree; [lia|auto]. }
    assert (distinct : left <> middle).
    { intro identity. subst middle. rewrite cube_equal_reflexive in equal. discriminate. }
    destruct left as [left low], middle as [middle high].
    rewrite associator_step_degree; try exact left_nonzero; try exact middle_nonzero; try exact distinct; try lia.
    + destruct (orb low high); [lia|]. pose proof (IHextra left middle). lia.
    + intros first second. specialize (IHextra first second). replace (S (S extra) - 2) with extra by lia. exact IHextra.
Qed.
Fixpoint pair_first_order (order : nat) : cube order -> cube order -> nat :=
  match order as size return cube size -> cube size -> nat with
  | 0 => fun _ _ => 0
  | S lower => fun left middle =>
      if orb (snd left) (snd middle) then S lower
      else pair_first_order lower (fst left) (fst middle)
  end.
Theorem pair_first_order_bound : forall order (left middle : cube order),
  pair_first_order order left middle <= order.
Proof.
  induction order; intros left middle; [reflexivity|].
  destruct left as [left low], middle as [middle high]. cbn [pair_first_order fst snd].
  destruct (orb low high); [lia|]. specialize (IHorder left middle). lia.
Qed.

Theorem associator_phase_degree : forall extra (left middle : cube (S (S (S extra)))),
  cube_nonzero (S (S (S extra))) left = true ->
  cube_nonzero (S (S (S extra))) middle = true -> left <> middle ->
  anf_degree (S (S (S extra))) (associator_phase (S (S (S extra))) left middle) =
  Nat.max 1 (pair_first_order (S (S (S extra))) left middle - 2).
Proof.
  induction extra; intros [left low] [middle high] left_nonzero middle_nonzero distinct.
  - rewrite associator_step_degree; try exact left_nonzero; try exact middle_nonzero; try exact distinct; try lia.
    2: { intros first second. exact (associator_degree_bound 0 first second). }
    assert (lower_zero : anf_degree 2 (associator_phase 2 left middle) = 0).
    { pose proof (associator_degree_bound 0 left middle). lia. }
    rewrite lower_zero. pose proof (pair_first_order_bound 3 (left, low) (middle, high)).
    destruct (orb low high); lia.
  - rewrite associator_step_degree; try exact left_nonzero; try exact middle_nonzero; try exact distinct; try lia.
    2: { intros first second. pose proof (associator_degree_bound (S extra) first second). lia. }
    change ((if orb low high then S (S (S extra)) - 1 else Nat.max (anf_degree (S (S (S extra))) (associator_phase (S (S (S extra))) left middle)) 1) =
      Nat.max 1 ((if orb low high then S (S (S (S extra))) else pair_first_order (S (S (S extra))) left middle) - 2)).
    destruct low, high; cbn [orb]; try lia.
    rewrite cube_nonzero_double, orb_false_r in left_nonzero, middle_nonzero.
    assert (lower_distinct : left <> middle) by (intro equal; apply distinct; now subst).
    rewrite IHextra by assumption. lia.
Qed.
Print Assumptions associator_degree_bound.
Print Assumptions associator_phase_degree.

Definition numeric_bit_length (value : nat) : nat :=
  if value =? 0 then 0 else S (Nat.log2 value).
Lemma numeric_bit_length_high : forall order value,
  2 ^ order <= value < 2 ^ S order -> numeric_bit_length value = S order.
Proof.
  intros order value bounds. unfold numeric_bit_length.
  assert (positive_power : 0 < 2 ^ order) by (pose proof (Nat.pow_nonzero 2 order); lia).
  assert (nonzero : (value =? 0) = false) by (apply Nat.eqb_neq; lia).
  rewrite nonzero. f_equal. apply Nat.log2_unique; lia.
Qed.
Theorem pair_first_order_numeric : forall order (left middle : cube order),
  pair_first_order order left middle =
  numeric_bit_length (Nat.max (cube_encode order left) (cube_encode order middle)).
Proof.
  induction order; intros left middle; [reflexivity|].
  destruct left as [left low], middle as [middle high].
  pose proof (cube_encode_bound order left) as left_bound.
  pose proof (cube_encode_bound order middle) as middle_bound.
  cbn [pair_first_order cube_encode fst snd]. destruct low, high; cbn [orb].
  - symmetry. apply numeric_bit_length_high. cbn [Nat.pow]. lia.
  - rewrite Nat.add_0_r. symmetry. apply numeric_bit_length_high. cbn [Nat.pow]. lia.
  - rewrite Nat.add_0_r. symmetry. apply numeric_bit_length_high. cbn [Nat.pow]. lia.
  - rewrite !Nat.add_0_r. apply IHorder.
Qed.
Corollary associator_degree_numeric_indices : forall extra (left middle : cube (S (S (S extra)))),
  cube_nonzero (S (S (S extra))) left = true ->
  cube_nonzero (S (S (S extra))) middle = true -> left <> middle ->
  anf_degree (S (S (S extra))) (associator_phase (S (S (S extra))) left middle) =
  Nat.max 1 (numeric_bit_length (Nat.max (cube_encode (S (S (S extra))) left)
    (cube_encode (S (S (S extra))) middle)) - 2).
Proof. intros. rewrite associator_phase_degree by assumption. rewrite pair_first_order_numeric. reflexivity. Qed.
Print Assumptions pair_first_order_numeric.
Print Assumptions associator_degree_numeric_indices.

Definition numeric_sign_row order fuel left (input : cube order) : bool :=
  Z.eqb (M3IsAssociator.cd_sign_fuel fuel (2 ^ order) left (cube_encode order input)) (-1).
Definition numeric_phase_row order fuel left middle (input : cube order) : bool :=
  Z.eqb (numeric_associator_sign order fuel left middle (cube_encode order input)) (-1).
Lemma numeric_sign_row_adapter : forall order fuel left input,
  order <= fuel ->
  numeric_sign_row order fuel (cube_encode order left) input = sign_exponent order left input.
Proof.
  intros. unfold numeric_sign_row. rewrite numeric_cube_sign by assumption.
  destruct (sign_exponent order left input); reflexivity.
Qed.
Lemma numeric_phase_row_adapter : forall order fuel left middle input,
  order <= fuel ->
  numeric_phase_row order fuel (cube_encode order left) (cube_encode order middle) input =
    associator_phase order left middle input.
Proof.
  intros. unfold numeric_phase_row. rewrite numeric_cube_associator by assumption.
  destruct (associator_phase order left middle input); reflexivity.
Qed.
Theorem numeric_sign_row_degree : forall extra fuel left,
  S (S extra) <= fuel -> 0 < left < 2 ^ S (S extra) ->
  anf_degree (S (S extra)) (numeric_sign_row (S (S extra)) fuel left) = S extra.
Proof.
  intros extra fuel left enough [positive bounded].
  rewrite <- (cube_encode_decode (S (S extra)) left bounded).
  transitivity (anf_degree (S (S extra)) (sign_exponent (S (S extra)) (cube_decode (S (S extra)) left))).
  - apply anf_degree_ext. intro input. apply numeric_sign_row_adapter. exact enough.
  - apply sign_row_degree. rewrite <- cube_encode_nonzero, cube_encode_decode by exact bounded.
    apply negb_true_iff, Nat.eqb_neq. lia.
Qed.
Theorem numeric_associator_phase_degree : forall extra fuel left middle,
  S (S (S extra)) <= fuel ->
  0 < left < 2 ^ S (S (S extra)) -> 0 < middle < 2 ^ S (S (S extra)) -> left <> middle ->
  anf_degree (S (S (S extra))) (numeric_phase_row (S (S (S extra))) fuel left middle) =
    Nat.max 1 (numeric_bit_length (Nat.max left middle) - 2).
Proof.
  intros extra fuel left middle enough [left_positive left_bound] [middle_positive middle_bound] distinct.
  rewrite <- (cube_encode_decode (S (S (S extra))) left left_bound),
    <- (cube_encode_decode (S (S (S extra))) middle middle_bound).
  transitivity (anf_degree (S (S (S extra))) (associator_phase (S (S (S extra)))
    (cube_decode (S (S (S extra))) left) (cube_decode (S (S (S extra))) middle))).
  - apply anf_degree_ext. intro input. apply numeric_phase_row_adapter. exact enough.
  - apply associator_degree_numeric_indices.
    + rewrite <- cube_encode_nonzero, cube_encode_decode by exact left_bound.
      apply negb_true_iff, Nat.eqb_neq. lia.
    + rewrite <- cube_encode_nonzero, cube_encode_decode by exact middle_bound.
      apply negb_true_iff, Nat.eqb_neq. lia.
    + intro equal. apply (f_equal (cube_encode (S (S (S extra))))) in equal.
      rewrite !cube_encode_decode in equal by assumption. contradiction.
Qed.
Example quaternion_degree_zero : anf_degree 2 (numeric_phase_row 2 2 1 2) = 0.
Proof. reflexivity. Qed.
Example embedded_pair_degree_one : anf_degree 4 (numeric_phase_row 4 4 1 2) = 1.
Proof. reflexivity. Qed.
Example new_sedenion_pair_degree_two : anf_degree 4 (numeric_phase_row 4 4 1 8) = 2.
Proof. reflexivity. Qed.
Print Assumptions numeric_sign_row_degree.
Print Assumptions numeric_associator_phase_degree.
