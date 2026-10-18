(** Degree is the maximum weight of a nonzero canonical ANF coefficient.
    The zero function has degree zero. *)
From Stdlib Require Import Arith Bool Lia btauto.Btauto.
From OpenGororoba Require Import SchreierSignCode.
Local Open Scope nat_scope.
Fixpoint cube_weight order : cube order -> nat :=
  match order with O => fun _ => 0 | S lower => fun mask =>
    cube_weight lower (fst mask) + if snd mask then 1 else 0 end.
Fixpoint cube_max order : (cube order -> nat) -> nat :=
  match order with O => fun function => function tt | S lower => fun function =>
    Nat.max (cube_max lower (fun input => function (input, false)))
      (cube_max lower (fun input => function (input, true))) end.
Definition coefficient_degree order (coefficients : cube order -> bool) :=
  cube_max order (fun mask => if coefficients mask then cube_weight order mask else 0).
Definition anf_degree order (function : cube order -> bool) :=
  coefficient_degree order (anf_evaluate order function).
Lemma cube_max_bound : forall order function bound,
  (forall input, function input <= bound) -> cube_max order function <= bound.
Proof.
  induction order; intros function bound bounded; [apply bounded|]. simpl.
  apply Nat.max_lub; apply IHorder; intro input; apply bounded.
Qed.
Lemma cube_max_member : forall order function input, function input <= cube_max order function.
Proof.
  induction order; intros; [destruct input; reflexivity|]. destruct input as [input high].
  cbn [cube_max]. destruct high.
  - eapply Nat.le_trans; [exact (IHorder (fun point => function (point, true)) input)|apply Nat.le_max_r].
  - eapply Nat.le_trans; [exact (IHorder (fun point => function (point, false)) input)|apply Nat.le_max_l].
Qed.
Lemma cube_weight_bound : forall order (mask : cube order), cube_weight order mask <= order.
Proof.
  induction order; intros; [reflexivity|]. destruct mask as [mask high].
  specialize (IHorder mask). cbn [cube_weight fst snd]. destruct high; lia.
Qed.
Lemma cube_weight_ones : forall order, cube_weight order (cube_ones order) = order.
Proof. induction order; simpl; lia. Qed.
Lemma cube_weight_full : forall order (mask : cube order),
  cube_weight order mask = order -> mask = cube_ones order.
Proof.
  induction order; intros mask full; [destruct mask; reflexivity|].
  destruct mask as [mask high]. pose proof (cube_weight_bound order mask).
  cbn [cube_weight fst snd] in full. destruct high; [|lia].
  assert (lower : cube_weight order mask = order) by lia.
  apply IHorder in lower. subst mask. reflexivity.
Qed.
Lemma monomial_ones : forall order (mask : cube order), monomial order mask (cube_ones order) = true.
Proof.
  induction order; intros; [reflexivity|]. destruct mask as [mask high].
  cbn [monomial cube_ones fst snd]. rewrite IHorder. destruct high; reflexivity.
Qed.
Theorem anf_degree_bound : forall order function, anf_degree order function <= order.
Proof.
  intros. unfold anf_degree, coefficient_degree. apply cube_max_bound. intro mask.
  destruct (anf_evaluate order function mask); [apply cube_weight_bound|lia].
Qed.
Lemma coefficient_witness_bound : forall order coefficients mask,
  coefficients mask = true -> cube_weight order mask <= coefficient_degree order coefficients.
Proof.
  intros. unfold coefficient_degree. pose proof (cube_max_member order
    (fun selected => if coefficients selected then cube_weight order selected else 0) mask) as bounded.
  cbn beta in bounded. rewrite H in bounded. exact bounded.
Qed.
Theorem canonical_anf_correct : forall order function input,
  anf_evaluate order (anf_evaluate order function) input = function input.
Proof. exact anf_evaluate_involutive. Qed.
Theorem canonical_anf_unique : forall order function coefficients,
  (forall input, anf_evaluate order coefficients input = function input) ->
  forall mask, coefficients mask = anf_evaluate order function mask.
Proof.
  intros order function coefficients equality mask.
  apply anf_evaluate_injective. intro input. rewrite equality, anf_evaluate_involutive. reflexivity.
Qed.
Theorem point_indicator_degree : forall order (target : cube order),
  anf_degree order (fun input => cube_equal order input target) = order.
Proof.
  intros. apply Nat.le_antisymm; [apply anf_degree_bound|].
  assert (lower : cube_weight order (cube_ones order) <=
    anf_degree order (fun input => cube_equal order input target)).
  { apply coefficient_witness_bound. rewrite anf_monomial_basis. apply monomial_ones. }
  rewrite cube_weight_ones in lower. exact lower.
Qed.
Lemma separating_coatom : forall order (left right : cube order), left <> right ->
  exists mask, cube_weight order mask = order - 1 /\
    monomial order left mask <> monomial order right mask.
Proof.
  induction order; intros left right different.
  - destruct left, right. contradiction.
  - destruct left as [left low], right as [right high].
    destruct (Bool.bool_dec low high) as [same|different_high].
    + subst high. assert (different_lower : left <> right) by (intro equal; subst; contradiction).
      destruct (IHorder left right different_lower) as [mask [weight separates]].
      assert (positive : 0 < order).
      { destruct order; [destruct left, right; contradiction|lia]. }
      exists (mask, true). split.
      * cbn [cube_weight fst snd]. lia.
      * cbn [monomial fst snd]. rewrite !orb_true_r, !andb_true_r. exact separates.
    + exists (cube_ones order, false). split.
      * cbn [cube_weight fst snd]. rewrite cube_weight_ones. lia.
      * cbn [monomial fst snd]. rewrite !monomial_ones.
        destruct low, high; simpl in *; congruence.
Qed.
Theorem two_point_indicator_degree : forall order (left right : cube order), left <> right ->
  anf_degree order (fun input => xorb (cube_equal order input left) (cube_equal order input right)) = order - 1.
Proof.
  intros order left right different. unfold anf_degree. apply Nat.le_antisymm.
  - unfold coefficient_degree. apply cube_max_bound. intro mask.
    rewrite anf_evaluate_xor, !anf_monomial_basis.
    destruct (xorb (monomial order left mask) (monomial order right mask)) eqn:nonzero; [|lia].
    pose proof (cube_weight_bound order mask).
    assert (not_full : cube_weight order mask <> order).
    { intro full. apply cube_weight_full in full. subst mask.
      rewrite !monomial_ones in nonzero. discriminate. }
    lia.
  - destruct (separating_coatom order left right different) as [mask [weight separates]].
    rewrite <- weight. apply coefficient_witness_bound.
    rewrite anf_evaluate_xor, !anf_monomial_basis.
    destruct (monomial order left mask), (monomial order right mask); simpl in *; try congruence.
Qed.
Print Assumptions canonical_anf_correct.
Print Assumptions canonical_anf_unique.
Print Assumptions point_indicator_degree.
Print Assumptions two_point_indicator_degree.

Lemma cube_max_ext : forall order first second,
  (forall mask, first mask = second mask) -> cube_max order first = cube_max order second.
Proof.
  induction order; intros first second equal; [apply equal|]. cbn [cube_max].
  rewrite (IHorder _ _ (fun mask => equal (mask, false))),
    (IHorder _ _ (fun mask => equal (mask, true))). reflexivity.
Qed.
Lemma cube_max_attained : forall order function,
  exists mask, function mask = cube_max order function.
Proof.
  induction order; intros function; [exists tt; reflexivity|].
  destruct (IHorder (fun mask => function (mask, false))) as [low low_value].
  destruct (IHorder (fun mask => function (mask, true))) as [high high_value].
  cbn [cube_max]. destruct (le_dec (function (low, false)) (function (high, true))) as [less|greater].
  - exists (high, true). rewrite <- low_value, <- high_value. symmetry. apply Nat.max_r. exact less.
  - exists (low, false). rewrite <- low_value, <- high_value. symmetry. apply Nat.max_l. lia.
Qed.
Lemma cube_weight_zero : forall order, cube_weight order (cube_zero order) = 0.
Proof. induction order; simpl; lia. Qed.
Theorem anf_degree_zero : forall order, anf_degree order (fun _ => false) = 0.
Proof.
  intros. apply Nat.le_antisymm; [|lia]. unfold anf_degree, coefficient_degree.
  apply cube_max_bound. intro mask. rewrite anf_evaluate_false. lia.
Qed.
Theorem anf_degree_xor_bound : forall order first second,
  anf_degree order (fun input => xorb (first input) (second input)) <=
  Nat.max (anf_degree order first) (anf_degree order second).
Proof.
  intros. unfold anf_degree at 1. unfold coefficient_degree. apply cube_max_bound. intro mask.
  rewrite anf_evaluate_xor.
  pose proof (coefficient_witness_bound order (anf_evaluate order first) mask) as first_bound.
  pose proof (coefficient_witness_bound order (anf_evaluate order second) mask) as second_bound.
  unfold anf_degree in *. destruct (anf_evaluate order first mask), (anf_evaluate order second mask);
    simpl; try (specialize (first_bound eq_refl)); try (specialize (second_bound eq_refl)); lia.
Qed.
Lemma anf_constant_coefficients : forall order constant mask,
  anf_evaluate order (fun _ => constant) mask = andb constant (cube_equal order mask (cube_zero order)).
Proof.
  intros. symmetry. exact (canonical_anf_unique order (fun _ => constant)
    (fun selected => andb constant (cube_equal order selected (cube_zero order)))
    (fun input => anf_scalar_delta order constant input) mask).
Qed.
Definition append_parity order (function : cube order -> bool) coefficient (input : cube (S order)) :=
  xorb (function (fst input)) (andb (snd input) coefficient).
Lemma append_parity_coefficients : forall order function coefficient mask high,
  anf_evaluate (S order) (append_parity order function coefficient) (mask, high) =
  if high then andb coefficient (cube_equal order mask (cube_zero order)) else anf_evaluate order function mask.
Proof.
  intros. unfold append_parity. cbn [anf_evaluate fst snd].
  transitivity (xorb (anf_evaluate order function mask)
    (andb high (anf_evaluate order (fun input => xorb (function input) coefficient) mask))).
  - f_equal.
    + apply anf_evaluate_extensional. intro input. destruct (function input); reflexivity.
  - rewrite anf_evaluate_xor, anf_constant_coefficients.
    destruct high, coefficient, (cube_equal order mask (cube_zero order)),
      (anf_evaluate order function mask); reflexivity.
Qed.
Theorem append_parity_degree : forall order function coefficient,
  anf_degree (S order) (append_parity order function coefficient) =
  Nat.max (anf_degree order function) (if coefficient then 1 else 0).
Proof.
  intros. unfold anf_degree at 1. unfold coefficient_degree at 1. cbn [cube_max].
  transitivity (Nat.max (anf_degree order function)
    (cube_max order (fun mask => if andb coefficient (cube_equal order mask (cube_zero order)) then 1 else 0))).
  - f_equal.
    + unfold anf_degree, coefficient_degree. apply cube_max_ext. intro mask.
      rewrite append_parity_coefficients. cbn [cube_weight fst snd]. rewrite Nat.add_0_r. reflexivity.
    + apply cube_max_ext. intro mask. rewrite append_parity_coefficients.
      destruct coefficient; [|reflexivity]. cbn [andb].
      destruct (cube_equal order mask (cube_zero order)) eqn:zero; [|reflexivity].
      apply cube_equal_spec in zero. subst mask. cbn [cube_weight fst snd]. rewrite cube_weight_zero. reflexivity.
  - f_equal. apply Nat.le_antisymm.
    + apply cube_max_bound. intro mask. destruct coefficient, (cube_equal order mask (cube_zero order)); simpl; lia.
    + pose proof (cube_max_member order
        (fun mask => if andb coefficient (cube_equal order mask (cube_zero order)) then 1 else 0)
        (cube_zero order)) as member.
      cbn beta in member. rewrite cube_equal_reflexive in member. destruct coefficient; exact member.
Qed.
Print Assumptions anf_degree_xor_bound.
Print Assumptions append_parity_degree.

Theorem anf_degree_strict_xor : forall order first second,
  anf_degree order first < anf_degree order second ->
  anf_degree order (fun input => xorb (first input) (second input)) = anf_degree order second.
Proof.
  intros order first second strict. apply Nat.le_antisymm.
  - eapply Nat.le_trans; [apply anf_degree_xor_bound|]. apply Nat.max_lub; lia.
  - destruct (cube_max_attained order (fun mask =>
      if anf_evaluate order second mask then cube_weight order mask else 0)) as [mask attained].
    change ((if anf_evaluate order second mask then cube_weight order mask else 0) = anf_degree order second) in attained.
    destruct (anf_evaluate order second mask) eqn:second_nonzero; [|lia].
    assert (first_zero : anf_evaluate order first mask = false).
    { destruct (anf_evaluate order first mask) eqn:nonzero; [|reflexivity].
      pose proof (coefficient_witness_bound order (anf_evaluate order first) mask nonzero).
      unfold anf_degree in strict, attained. lia. }
    assert (lower : cube_weight order mask <=
      anf_degree order (fun input => xorb (first input) (second input))).
    { apply coefficient_witness_bound. rewrite anf_evaluate_xor, first_zero, second_nonzero. reflexivity. }
    rewrite attained in lower. exact lower.
Qed.
Theorem anf_degree_constant : forall order constant, anf_degree order (fun _ => constant) = 0.
Proof.
  intros. apply Nat.le_antisymm; [|lia]. unfold anf_degree, coefficient_degree.
  apply cube_max_bound. intro mask. rewrite anf_constant_coefficients.
  destruct constant; [|reflexivity]. cbn [andb].
  destruct (cube_equal order mask (cube_zero order)) eqn:zero; [|lia].
  apply cube_equal_spec in zero. subst mask. rewrite cube_weight_zero. lia.
Qed.
Print Assumptions anf_degree_strict_xor.
Print Assumptions anf_degree_constant.

Theorem anf_degree_ext : forall order first second,
  (forall input, first input = second input) -> anf_degree order first = anf_degree order second.
Proof.
  intros. unfold anf_degree, coefficient_degree. apply cube_max_ext. intro mask.
  rewrite (anf_evaluate_extensional order first second H mask). reflexivity.
Qed.
Lemma monomial_coefficients : forall order mask selected,
  anf_evaluate order (monomial order mask) selected = cube_equal order selected mask.
Proof.
  intros. transitivity (anf_evaluate order
    (anf_evaluate order (fun input => cube_equal order input mask)) selected).
  - apply anf_evaluate_extensional. intro input. symmetry. apply anf_monomial_basis.
  - exact (anf_evaluate_involutive order (fun input => cube_equal order input mask) selected).
Qed.
Theorem monomial_degree : forall order mask, anf_degree order (monomial order mask) = cube_weight order mask.
Proof.
  intros. apply Nat.le_antisymm.
  - unfold anf_degree, coefficient_degree. apply cube_max_bound. intro selected.
    rewrite monomial_coefficients. destruct (cube_equal order selected mask) eqn:equal; [|lia].
    apply cube_equal_spec in equal. subst selected. lia.
  - apply coefficient_witness_bound. rewrite monomial_coefficients. apply cube_equal_reflexive.
Qed.
Print Assumptions monomial_degree.

Definition append_boolean order (first second : cube order -> bool) (input : cube (S order)) :=
  xorb (first (fst input)) (andb (snd input) (second (fst input))).
Lemma append_boolean_coefficients : forall order first second mask high,
  anf_evaluate (S order) (append_boolean order first second) (mask, high) =
  if high then anf_evaluate order second mask else anf_evaluate order first mask.
Proof.
  intros. unfold append_boolean. cbn [anf_evaluate fst snd].
  transitivity (xorb (anf_evaluate order first mask)
    (andb high (anf_evaluate order (fun input => xorb (first input) (second input)) mask))).
  - f_equal. apply anf_evaluate_extensional. intro input. destruct (first input); reflexivity.
  - rewrite anf_evaluate_xor. destruct high, (anf_evaluate order first mask), (anf_evaluate order second mask); reflexivity.
Qed.
Lemma nonzero_degree_attained : forall order coefficients,
  (exists mask, coefficients mask = true) ->
  exists mask, coefficients mask = true /\ cube_weight order mask = coefficient_degree order coefficients.
Proof.
  intros order coefficients [initial nonzero].
  destruct (Nat.eq_dec (coefficient_degree order coefficients) 0) as [zero|positive].
  - exists initial. split; [exact nonzero|].
    pose proof (coefficient_witness_bound order coefficients initial nonzero). lia.
  - destruct (cube_max_attained order (fun mask => if coefficients mask then cube_weight order mask else 0)) as [mask attained].
    change ((if coefficients mask then cube_weight order mask else 0) = coefficient_degree order coefficients) in attained.
    destruct (coefficients mask) eqn:selected; [exists mask; auto|lia].
Qed.
Theorem append_boolean_degree : forall order first second,
  (exists mask, anf_evaluate order second mask = true) ->
  anf_degree (S order) (append_boolean order first second) =
  Nat.max (anf_degree order first) (S (anf_degree order second)).
Proof.
  intros order first second nonzero.
  unfold anf_degree at 1. unfold coefficient_degree at 1. cbn [cube_max].
  transitivity (Nat.max (anf_degree order first)
    (cube_max order (fun mask => if anf_evaluate order second mask then S (cube_weight order mask) else 0))).
  - f_equal.
    + unfold anf_degree, coefficient_degree. apply cube_max_ext. intro mask.
      rewrite append_boolean_coefficients. cbn [cube_weight fst snd]. rewrite Nat.add_0_r. reflexivity.
    + apply cube_max_ext. intro mask. rewrite append_boolean_coefficients.
      cbn [cube_weight fst snd]. destruct (anf_evaluate order second mask); f_equal; lia.
  - f_equal. apply Nat.le_antisymm.
    + apply cube_max_bound. intro mask. destruct (anf_evaluate order second mask) eqn:selected; [|lia].
      pose proof (coefficient_witness_bound order (anf_evaluate order second) mask selected). unfold anf_degree. lia.
    + destruct (nonzero_degree_attained order (anf_evaluate order second) nonzero) as [mask [selected attained]].
      pose proof (cube_max_member order
        (fun selected_mask => if anf_evaluate order second selected_mask then S (cube_weight order selected_mask) else 0) mask) as member.
      cbn beta in member. rewrite selected, attained in member. exact member.
Qed.
Lemma positive_degree_has_coefficient : forall order function, 0 < anf_degree order function ->
  exists mask, anf_evaluate order function mask = true.
Proof.
  intros order function positive. destruct (cube_max_attained order
    (fun mask => if anf_evaluate order function mask then cube_weight order mask else 0)) as [mask attained].
  change ((if anf_evaluate order function mask then cube_weight order mask else 0) = anf_degree order function) in attained.
  destruct (anf_evaluate order function mask) eqn:nonzero; [exists mask; exact nonzero|lia].
Qed.
Theorem anf_degree_add_constant : forall order function constant,
  0 < anf_degree order function ->
  anf_degree order (fun input => xorb (function input) constant) = anf_degree order function.
Proof.
  intros order function constant positive.
  transitivity (anf_degree order (fun input => xorb constant (function input))).
  - apply anf_degree_ext. intro input. apply xorb_comm.
  - apply anf_degree_strict_xor. rewrite anf_degree_constant. exact positive.
Qed.
Print Assumptions append_boolean_degree.
Print Assumptions anf_degree_add_constant.
