(** Canonical cosets use finite minimization of numeric cube coordinates. *)
From Stdlib Require Import Arith Bool Lia List btauto.Btauto.
From OpenGororoba Require Import SchreierSignCode CDAssociatorDoubling CDSignNumericCorrespondence CDPhaseDegree WalshProbability.
Import ListNotations.
Local Open Scope nat_scope.
Record xor_subgroup order := {
  subgroup_member : cube order -> bool;
  subgroup_zero : subgroup_member (cube_zero order) = true;
  subgroup_xor : forall left right,
    subgroup_member left = true -> subgroup_member right = true ->
    subgroup_member (cube_xor order left right) = true
}.
Arguments subgroup_member {order}.
Definition same_coset order (group : xor_subgroup order) (left right : cube order) :=
  subgroup_member group (cube_xor order left right).
Lemma same_coset_reflexive : forall order group (input : cube order), same_coset order group input input = true.
Proof. intros. unfold same_coset. rewrite phase_cube_xor_self. apply subgroup_zero. Qed.
Lemma same_coset_symmetric : forall order group (left right : cube order),
  same_coset order group left right = same_coset order group right left.
Proof. intros. unfold same_coset. rewrite cube_xor_commutative. reflexivity. Qed.
Lemma cube_xor_associative : forall order (first middle last : cube order),
  cube_xor order first (cube_xor order middle last) = cube_xor order (cube_xor order first middle) last.
Proof.
  induction order; intros first middle last; [reflexivity|].
  destruct first as [first low], middle as [middle high], last as [last top].
  cbn [cube_xor fst snd]. rewrite IHorder. f_equal. symmetry. apply xorb_assoc.
Qed.
Lemma same_coset_transitive : forall order group (first middle last : cube order),
  same_coset order group first middle = true -> same_coset order group middle last = true ->
  same_coset order group first last = true.
Proof.
  intros order group first middle last first_middle middle_last.
  pose proof (subgroup_xor order group _ _ first_middle middle_last) as combined.
  unfold same_coset in *. rewrite <- cube_xor_associative,
    (cube_xor_associative order middle middle last), phase_cube_xor_self,
    (cube_xor_commutative order (cube_zero order) last), cube_xor_zero in combined.
  exact combined.
Qed.
Lemma cube_points_complete : forall order (input : cube order), In input (cube_points order).
Proof.
  induction order; intros input; [destruct input; simpl; auto|].
  destruct input as [input high]. cbn [cube_points]. apply in_or_app.
  destruct high; [right|left]; apply in_map_iff; exists input; split; try reflexivity; apply IHorder.
Qed.
Fixpoint coset_minimum order (group : xor_subgroup order) (input : cube order)
  (candidates : list (cube order)) (seed : cube order) : cube order :=
  match candidates with
  | [] => seed
  | candidate :: remaining =>
      let best := coset_minimum order group input remaining seed in
      if andb (same_coset order group input candidate)
        (cube_encode order candidate <? cube_encode order best) then candidate else best
  end.
Lemma coset_minimum_member : forall order group input candidates seed,
  same_coset order group input seed = true ->
  same_coset order group input (coset_minimum order group input candidates seed) = true.
Proof.
  intros order group input candidates. induction candidates as [|candidate remaining induction]; intros seed valid; [exact valid|].
  cbn [coset_minimum]. destruct (andb (same_coset order group input candidate)
    (cube_encode order candidate <? cube_encode order (coset_minimum order group input remaining seed))) eqn:selected.
  - apply andb_true_iff in selected. tauto.
  - apply induction. exact valid.
Qed.
Lemma coset_minimum_seed_bound : forall order group input candidates seed,
  cube_encode order (coset_minimum order group input candidates seed) <= cube_encode order seed.
Proof.
  intros order group input candidates. induction candidates as [|candidate remaining induction]; intro seed; [reflexivity|].
  cbn [coset_minimum]. destruct (andb (same_coset order group input candidate)
    (cube_encode order candidate <? cube_encode order (coset_minimum order group input remaining seed))) eqn:selected.
  - apply andb_true_iff in selected. destruct selected as [_ bound]. apply Nat.ltb_lt in bound.
    specialize (induction seed). lia.
  - apply induction.
Qed.
Lemma coset_minimum_candidate_bound : forall order group input candidates seed candidate,
  In candidate candidates -> same_coset order group input candidate = true ->
  cube_encode order (coset_minimum order group input candidates seed) <= cube_encode order candidate.
Proof.
  intros order group input candidates. induction candidates as [|first remaining induction]; intros seed candidate member valid; [contradiction|].
  cbn [coset_minimum]. destruct (andb (same_coset order group input first)
    (cube_encode order first <? cube_encode order (coset_minimum order group input remaining seed))) eqn:selected.
  - apply andb_true_iff in selected. destruct selected as [_ bound]. apply Nat.ltb_lt in bound.
    destruct member as [equal|member]; [subst; reflexivity|]. specialize (induction seed candidate member valid). lia.
  - destruct member as [equal|member].
    + subst first. rewrite valid in selected. cbn [andb] in selected. apply Nat.ltb_ge in selected. exact selected.
    + apply induction; assumption.
Qed.
Definition coset_representative order group (input : cube order) :=
  coset_minimum order group input (cube_points order) input.
Theorem coset_representative_member : forall order group input,
  same_coset order group input (coset_representative order group input) = true.
Proof. intros. apply coset_minimum_member, same_coset_reflexive. Qed.
Theorem coset_representative_minimal : forall order group input candidate,
  same_coset order group input candidate = true ->
  cube_encode order (coset_representative order group input) <= cube_encode order candidate.
Proof. intros. apply coset_minimum_candidate_bound; [apply cube_points_complete|assumption]. Qed.
Theorem same_coset_representatives : forall order group (left right : cube order),
  same_coset order group left right = true ->
  coset_representative order group left = coset_representative order group right.
Proof.
  intros order group left right equivalent. apply cube_encode_injective, Nat.le_antisymm.
  - apply coset_representative_minimal. eapply same_coset_transitive; [exact equivalent|apply coset_representative_member].
  - apply coset_representative_minimal. eapply same_coset_transitive.
    + rewrite same_coset_symmetric. exact equivalent.
    + apply coset_representative_member.
Qed.
Theorem complete_coset_partition : forall order group (left right : cube order),
  same_coset order group left right = true <->
  coset_representative order group left = coset_representative order group right.
Proof.
  intros order group left right. split; [apply same_coset_representatives|].
  intro equal. eapply same_coset_transitive; [apply coset_representative_member|].
  rewrite equal, same_coset_symmetric. apply coset_representative_member.
Qed.
Theorem coset_representative_idempotent : forall order group input,
  coset_representative order group (coset_representative order group input) = coset_representative order group input.
Proof. intros. symmetry. apply same_coset_representatives, coset_representative_member. Qed.
Print Assumptions complete_coset_partition.

Theorem canonical_sector_gate : forall order group (sector input : cube order),
  andb (cube_equal order (coset_representative order group sector) sector)
    (same_coset order group input sector) =
  cube_equal order sector (coset_representative order group input).
Proof.
  intros order group sector input.
  assert (forward : andb (cube_equal order (coset_representative order group sector) sector)
    (same_coset order group input sector) = true ->
    cube_equal order sector (coset_representative order group input) = true).
  { intro selected. apply andb_true_iff in selected. destruct selected as [fixed related].
    apply cube_equal_spec in fixed. apply cube_equal_spec.
    rewrite <- fixed. symmetry. apply same_coset_representatives. exact related. }
  assert (backward : cube_equal order sector (coset_representative order group input) = true ->
    andb (cube_equal order (coset_representative order group sector) sector)
      (same_coset order group input sector) = true).
  { intro equal. apply cube_equal_spec in equal. subst sector.
    rewrite coset_representative_idempotent, cube_equal_reflexive, coset_representative_member. reflexivity. }
  destruct (andb (cube_equal order (coset_representative order group sector) sector)
    (same_coset order group input sector)), (cube_equal order sector (coset_representative order group input));
    try reflexivity; [specialize (forward eq_refl)|specialize (backward eq_refl)]; discriminate.
Qed.
Print Assumptions canonical_sector_gate.
Lemma same_coset_equivalent_left : forall order group (left middle right : cube order),
  same_coset order group left middle = true ->
  same_coset order group left right = same_coset order group middle right.
Proof.
  intros order group left middle right equivalent.
  destruct (same_coset order group left right) eqn:first, (same_coset order group middle right) eqn:second;
    try reflexivity.
  - assert (result : same_coset order group middle right = true).
    { eapply same_coset_transitive; [rewrite same_coset_symmetric; exact equivalent|exact first]. }
    congruence.
  - assert (result : same_coset order group left right = true) by (eapply same_coset_transitive; eassumption).
    congruence.
Qed.

Lemma cube_xor_four_swap : forall order (first second third fourth : cube order),
  cube_xor order (cube_xor order first second) (cube_xor order third fourth) =
  cube_xor order (cube_xor order first third) (cube_xor order second fourth).
Proof.
  induction order; intros first second third fourth; [reflexivity|].
  destruct first as [first low], second as [second high], third as [third top], fourth as [fourth last].
  cbn [cube_xor fst snd]. rewrite IHorder. f_equal. btauto.
Qed.
Lemma same_coset_translation : forall order group (anchor left right : cube order),
  same_coset order group (cube_xor order anchor left) (cube_xor order anchor right) =
    same_coset order group left right.
Proof.
  intros. unfold same_coset. rewrite cube_xor_four_swap, phase_cube_xor_self,
    (cube_xor_commutative order (cube_zero order) (cube_xor order left right)), cube_xor_zero. reflexivity.
Qed.

Definition pair_xor_subgroup order (label : cube order) : xor_subgroup order.
Proof.
  refine {| subgroup_member := fun input => orb (cube_equal order input (cube_zero order)) (cube_equal order input label) |}.
  - rewrite cube_equal_reflexive. reflexivity.
  - intros left right left_member right_member. apply orb_true_iff in left_member, right_member.
    destruct left_member as [left_condition|left_condition], right_member as [right_condition|right_condition];
      apply cube_equal_spec in left_condition; apply cube_equal_spec in right_condition; subst left; subst right.
    + rewrite cube_xor_zero, cube_equal_reflexive. reflexivity.
    + rewrite (cube_xor_commutative order (cube_zero order) label), cube_xor_zero, cube_equal_reflexive, orb_true_r. reflexivity.
    + rewrite cube_xor_zero, cube_equal_reflexive, orb_true_r. reflexivity.
    + rewrite phase_cube_xor_self, cube_equal_reflexive. reflexivity.
Defined.
Theorem pair_xor_coset_members : forall order (left upper : cube order),
  same_coset order (pair_xor_subgroup order (cube_xor order left upper)) left left = true /\
  same_coset order (pair_xor_subgroup order (cube_xor order left upper)) upper left = true.
Proof.
  intros. split; [apply same_coset_reflexive|]. unfold same_coset. cbn [pair_xor_subgroup subgroup_member].
  rewrite (cube_xor_commutative order upper left), cube_equal_reflexive, orb_true_r. reflexivity.
Qed.
Print Assumptions pair_xor_subgroup.
Print Assumptions pair_xor_coset_members.
