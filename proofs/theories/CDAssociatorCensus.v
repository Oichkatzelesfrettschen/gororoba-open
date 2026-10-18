(** Ordered basis-triple counts use exact integer phase sums. *)
From Stdlib Require Import Arith Bool Lia ZArith ZArithRing btauto.Btauto.
From OpenGororoba Require Import SchreierSignCode CDAssociatorDoubling CDPhaseDegree CDSignNumericCorrespondence WalshProbability.
Local Open Scope nat_scope.
Lemma census_pair_zero_left : forall order (value : cube order),
  pair_coefficient order (cube_zero order) value = false.
Proof.
  intros. unfold pair_coefficient. rewrite cube_nonzero_zero,
    (cube_xor_commutative order (cube_zero order) value), cube_xor_zero. btauto.
Qed.
Lemma census_pair_zero_right : forall order (value : cube order),
  pair_coefficient order value (cube_zero order) = false.
Proof. intros. unfold pair_coefficient. rewrite cube_nonzero_zero, cube_xor_zero. btauto. Qed.
Lemma census_pair_diagonal : forall order (value : cube order),
  pair_coefficient order value value = false.
Proof. intros. unfold pair_coefficient. rewrite phase_cube_xor_self, cube_nonzero_zero. btauto. Qed.
Lemma census_pair_false : forall order (left right : cube order),
  pair_coefficient order left right = false <->
  left = cube_zero order \/ right = cube_zero order \/ left = right.
Proof.
  intros order left right. split.
  - intro vanishes. destruct (cube_nonzero order left) eqn:left_zero.
    + destruct (cube_nonzero order right) eqn:right_zero.
      * destruct (cube_equal order left right) eqn:equal.
        -- right; right. now apply cube_equal_spec.
        -- assert (distinct : left <> right) by (intro identity; subst; rewrite cube_equal_reflexive in equal; discriminate).
           rewrite independent_pair_coefficient in vanishes by assumption. discriminate.
      * right; left. unfold cube_nonzero in right_zero. now apply negb_false_iff, cube_equal_spec in right_zero.
    + left. unfold cube_nonzero in left_zero. now apply negb_false_iff, cube_equal_spec in left_zero.
  - intros [zero|[zero|equal]]; subst; auto using census_pair_zero_left, census_pair_zero_right, census_pair_diagonal.
Qed.
Lemma census_pair_translate : forall order (left right : cube order),
  pair_coefficient order left (cube_xor order left right) = pair_coefficient order left right.
Proof. intros. unfold pair_coefficient. rewrite phase_cube_xor_involution. btauto. Qed.
Definition thin_triple order (left middle right : cube order) :=
  negb (orb (pair_coefficient order left middle)
    (orb (pair_coefficient order left right) (pair_coefficient order middle right))).
Lemma census_top_coefficients : forall order (left middle right : cube order),
  andb (negb (pair_coefficient order left middle))
    (andb (negb (pair_coefficient order middle right))
      (negb (xorb (pair_coefficient order left middle)
        (pair_coefficient order left (cube_xor order middle right))))) =
    thin_triple order left middle right.
Proof.
  intros order left middle right. unfold thin_triple.
  destruct (pair_coefficient order left middle) eqn:pair; [reflexivity|].
  apply census_pair_false in pair. destruct pair as [zero|[zero|equal]].
  - subst left. rewrite !census_pair_zero_left. destruct (pair_coefficient order middle right); reflexivity.
  - subst middle. rewrite census_pair_zero_left,
      (cube_xor_commutative order (cube_zero order) right), cube_xor_zero. destruct (pair_coefficient order left right); reflexivity.
  - subst middle. rewrite census_pair_translate. destruct (pair_coefficient order left right); reflexivity.
Qed.
Theorem census_top_bit_law : forall order (left middle right : cube order) low high top,
  associator_phase (S order) (left,low) (middle,high) (right,top) =
  xorb (associator_phase order left middle right)
    (xorb (andb low (pair_coefficient order middle right))
      (xorb (andb high (xorb (pair_coefficient order left middle)
        (pair_coefficient order left (cube_xor order middle right))))
        (andb top (pair_coefficient order left middle)))).
Proof.
  intros. pose proof (lower_pair_lifting order left middle right true) as last_coefficient.
  rewrite associator_doubling in last_coefficient.
  rewrite !commutation_pair_coefficient in last_coefficient.
  assert (cancel : forall first second third, xorb first second = xorb first third -> second = third).
  { intros [] [] []; simpl; congruence. }
  change (xorb (associator_phase order left middle right)
    (xorb (pair_coefficient order (cube_xor order left middle) right)
      (xorb (pair_coefficient order middle right) (pair_coefficient order left (cube_xor order middle right)))) =
    xorb (associator_phase order left middle right) (pair_coefficient order left middle)) in last_coefficient.
  apply cancel in last_coefficient.
  rewrite associator_doubling, !commutation_pair_coefficient, last_coefficient.
  reflexivity.
Qed.

Definition boolean_triple_sum (function : bool -> bool -> bool -> Z) : Z :=
  (function false false false + function false false true +
   function false true false + function false true true +
   function true false false + function true false true +
   function true true false + function true true true)%Z.
Lemma census_boolean_character : forall phase first second third,
  boolean_triple_sum (fun low high top => phase_sign
    (xorb phase (xorb (andb low first) (xorb (andb high second) (andb top third))))) =
  (if andb (negb first) (andb (negb second) (negb third)) then 8 * phase_sign phase else 0)%Z.
Proof. intros [] [] [] []; reflexivity. Qed.
Lemma census_thin_associates : forall order (left middle right : cube order),
  thin_triple order left middle right = true -> associator_phase order left middle right = false.
Proof.
  intros order left middle right thin. unfold thin_triple in thin.
  apply negb_true_iff, orb_false_iff in thin. destruct thin as [dependent _].
  apply census_pair_false in dependent. destruct dependent as [zero|[zero|equal]].
  - subst left. apply (proj1 (degenerate_associator_zero order middle right)).
  - subst middle. apply (proj1 (proj2 (degenerate_associator_zero order left right))).
  - subst middle. apply (proj2 (proj2 (degenerate_associator_zero order left right))).
Qed.
Theorem census_top_bit_cancellation : forall order (left middle right : cube order),
  boolean_triple_sum (fun low high top => phase_sign
    (associator_phase (S order) (left,low) (middle,high) (right,top))) =
  (if thin_triple order left middle right then 8 else 0)%Z.
Proof.
  intros. unfold boolean_triple_sum. rewrite !census_top_bit_law.
  change (boolean_triple_sum (fun low high top => phase_sign
    (xorb (associator_phase order left middle right)
      (xorb (andb low (pair_coefficient order middle right))
        (xorb (andb high (xorb (pair_coefficient order left middle)
          (pair_coefficient order left (cube_xor order middle right))))
          (andb top (pair_coefficient order left middle)))))) = (if thin_triple order left middle right then 8 else 0)%Z).
  rewrite census_boolean_character.
  assert (coefficient : andb (negb (pair_coefficient order middle right))
    (andb (negb (xorb (pair_coefficient order left middle)
      (pair_coefficient order left (cube_xor order middle right))))
      (negb (pair_coefficient order left middle))) = thin_triple order left middle right).
  { rewrite <- census_top_coefficients. btauto. }
  rewrite coefficient. destruct (thin_triple order left middle right) eqn:thin; [|reflexivity].
  rewrite census_thin_associates by exact thin. reflexivity.
Qed.

Local Open Scope Z_scope.
Definition census_delta order (target input : cube order) : Z :=
  if cube_equal order input target then 1 else 0.
Lemma census_delta_sum : forall order (target : cube order),
  integer_cube_sum order (census_delta order target) = 1.
Proof.
  induction order; intros target; [destruct target; reflexivity|].
  destruct target as [target high].
  assert (slice : forall bit, integer_cube_sum order (fun input =>
    census_delta (S order) (target,high) (input,bit)) = if Bool.eqb bit high then 1 else 0).
  { intro bit. unfold census_delta. cbn [cube_equal fst snd].
    destruct (Bool.eqb bit high) eqn:equal.
    - transitivity (integer_cube_sum order (census_delta order target)); [|apply IHorder].
      apply integer_cube_sum_ext. intro input. unfold census_delta. destruct (cube_equal order input target); reflexivity.
    - transitivity (integer_cube_sum order (fun _ => 0)); [|rewrite integer_cube_sum_constant; ring].
      apply integer_cube_sum_ext. intro input. destruct (cube_equal order input target); reflexivity. }
  change ((integer_cube_sum order (fun input => census_delta (S order) (target,high) (input,false)) +
    integer_cube_sum order (fun input => census_delta (S order) (target,high) (input,true))) = 1).
  rewrite !slice. destruct high; reflexivity.
Qed.
Lemma census_sum_single_exception : forall order (target : cube order) ordinary exceptional,
  integer_cube_sum order (fun input => if cube_equal order input target then exceptional else ordinary) =
  Z.of_nat (Nat.pow 2 order) * ordinary + (exceptional - ordinary).
Proof.
  intros. transitivity (integer_cube_sum order (fun input =>
    ordinary + (exceptional - ordinary) * census_delta order target input)).
  - apply integer_cube_sum_ext. intro input. unfold census_delta.
    destruct (cube_equal order input target); ring.
  - rewrite integer_cube_sum_add, integer_cube_sum_constant, integer_cube_sum_scale, census_delta_sum. ring.
Qed.
Lemma census_pair_zero_mask : forall order (left input : cube order),
  cube_nonzero order left = true ->
  (if pair_coefficient order left input then 0 else 1) =
  census_delta order (cube_zero order) input + census_delta order left input.
Proof.
  intros order left input nonzero. rewrite pair_coefficient_delta, nonzero.
  unfold census_delta. destruct (cube_equal order input (cube_zero order)) eqn:zero,
    (cube_equal order input left) eqn:equal; try reflexivity.
  apply cube_equal_spec in zero, equal. subst input. apply (cube_zero_distinct order left nonzero) in equal. contradiction.
Qed.
Lemma census_pair_zero_count : forall order (left : cube order),
  integer_cube_sum order (fun input => if pair_coefficient order left input then 0 else 1) =
  if cube_nonzero order left then 2 else Z.of_nat (Nat.pow 2 order).
Proof.
  intros. destruct (cube_nonzero order left) eqn:nonzero.
  - transitivity (integer_cube_sum order (fun input =>
      census_delta order (cube_zero order) input + census_delta order left input)).
    + apply integer_cube_sum_ext. intro input. apply census_pair_zero_mask. exact nonzero.
    + rewrite integer_cube_sum_add, !census_delta_sum. reflexivity.
  - unfold cube_nonzero in nonzero. apply negb_false_iff, cube_equal_spec in nonzero. subst left.
    transitivity (integer_cube_sum order (fun _ => 1)).
    + apply integer_cube_sum_ext. intro input. rewrite census_pair_zero_left. reflexivity.
    + rewrite integer_cube_sum_constant. ring.
Qed.
Lemma census_thin_inner : forall order (left middle right : cube order),
  thin_triple order left middle right =
  if pair_coefficient order left middle then false else
    if cube_nonzero order left then negb (pair_coefficient order left right)
    else negb (pair_coefficient order middle right).
Proof.
  intros order left middle right. unfold thin_triple.
  destruct (pair_coefficient order left middle) eqn:pair; [reflexivity|].
  apply census_pair_false in pair. destruct pair as [zero|[zero|equal]].
  - subst left. rewrite census_pair_zero_left, cube_nonzero_zero. reflexivity.
  - subst middle. rewrite census_pair_zero_left.
    destruct (cube_nonzero order left) eqn:nonzero; [destruct (pair_coefficient order left right); reflexivity|].
    unfold cube_nonzero in nonzero. apply negb_false_iff, cube_equal_spec in nonzero. subst left.
    rewrite census_pair_zero_left. reflexivity.
  - subst middle. destruct (cube_nonzero order left); destruct (pair_coefficient order left right); reflexivity.
Qed.
Lemma census_thin_completion_count : forall order (left middle : cube order),
  integer_cube_sum order (fun right => if thin_triple order left middle right then 1 else 0) =
  if pair_coefficient order left middle then 0 else
    if cube_nonzero order left then 2 else
      if cube_nonzero order middle then 2 else Z.of_nat (Nat.pow 2 order).
Proof.
  intros order left middle.
  transitivity (integer_cube_sum order (fun right =>
    if (if pair_coefficient order left middle then false else
      if cube_nonzero order left then negb (pair_coefficient order left right)
      else negb (pair_coefficient order middle right)) then 1 else 0)).
  { apply integer_cube_sum_ext. intro right. rewrite census_thin_inner. reflexivity. }
  destruct (pair_coefficient order left middle) eqn:pair.
  - rewrite integer_cube_sum_constant. ring.
  - destruct (cube_nonzero order left) eqn:nonzero.
    + transitivity (integer_cube_sum order (fun right => if pair_coefficient order left right then 0 else 1)).
      * apply integer_cube_sum_ext. intro right. destruct (pair_coefficient order left right); reflexivity.
      * rewrite census_pair_zero_count, nonzero. reflexivity.
    + transitivity (integer_cube_sum order (fun right => if pair_coefficient order middle right then 0 else 1)).
      * apply integer_cube_sum_ext. intro right. destruct (pair_coefficient order middle right); reflexivity.
      * apply census_pair_zero_count.
Qed.
Lemma census_thin_pair_count : forall order (left : cube order),
  integer_cube_sum order (fun middle => integer_cube_sum order
    (fun right => if thin_triple order left middle right then 1 else 0)) =
  if cube_nonzero order left then 4 else 3 * Z.of_nat (Nat.pow 2 order) - 2.
Proof.
  intros order left. destruct (cube_nonzero order left) eqn:nonzero.
  - transitivity (integer_cube_sum order (fun middle =>
      2 * (if pair_coefficient order left middle then 0 else 1))).
    + apply integer_cube_sum_ext. intro middle. rewrite census_thin_completion_count, nonzero.
      destruct (pair_coefficient order left middle); reflexivity.
    + rewrite integer_cube_sum_scale, census_pair_zero_count, nonzero. reflexivity.
  - assert (left_zero : left = cube_zero order).
    { unfold cube_nonzero in nonzero. now apply negb_false_iff, cube_equal_spec in nonzero. }
    subst left. transitivity (integer_cube_sum order (fun middle =>
      if cube_equal order middle (cube_zero order) then Z.of_nat (Nat.pow 2 order) else 2)).
    + apply integer_cube_sum_ext. intro middle. rewrite census_thin_completion_count, census_pair_zero_left, cube_nonzero_zero.
      unfold cube_nonzero. destruct (cube_equal order middle (cube_zero order)); reflexivity.
    + rewrite census_sum_single_exception. ring.
Qed.
Definition census_triple_sum order (function : cube order -> cube order -> cube order -> Z) :=
  integer_cube_sum order (fun left => integer_cube_sum order (fun middle =>
    integer_cube_sum order (fun right => function left middle right))).
Theorem census_thin_triple_count : forall order,
  census_triple_sum order (fun left middle right => if thin_triple order left middle right then 1 else 0) =
  7 * Z.of_nat (Nat.pow 2 order) - 6.
Proof.
  intro order. unfold census_triple_sum.
  transitivity (integer_cube_sum order (fun left =>
    if cube_equal order left (cube_zero order) then 3 * Z.of_nat (Nat.pow 2 order) - 2 else 4)).
  - apply integer_cube_sum_ext. intro left. rewrite census_thin_pair_count.
    unfold cube_nonzero. destruct (cube_equal order left (cube_zero order)); reflexivity.
  - rewrite census_sum_single_exception. ring.
Qed.
Lemma census_triple_slices : forall order function,
  census_triple_sum (S order) function =
  census_triple_sum order (fun left middle right => boolean_triple_sum
    (fun low high top => function (left,low) (middle,high) (right,top))).
Proof.
  intros. unfold census_triple_sum. cbn [integer_cube_sum boolean_triple_sum].
  unfold boolean_triple_sum. rewrite <- integer_cube_sum_add.
  apply integer_cube_sum_ext. intro left. repeat rewrite <- integer_cube_sum_add.
  apply integer_cube_sum_ext. intro middle. repeat rewrite <- integer_cube_sum_add.
  apply integer_cube_sum_ext. intro right. ring.
Qed.
Lemma census_triple_scale : forall order factor function,
  census_triple_sum order (fun left middle right => factor * function left middle right) =
  factor * census_triple_sum order function.
Proof.
  intros. unfold census_triple_sum. rewrite <- integer_cube_sum_scale.
  apply integer_cube_sum_ext. intro left. rewrite <- integer_cube_sum_scale.
  apply integer_cube_sum_ext. intro middle. apply integer_cube_sum_scale.
Qed.
Theorem census_total_phase_sum : forall order,
  census_triple_sum (S order) (fun left middle right => phase_sign
    (associator_phase (S order) left middle right)) =
  8 * (7 * Z.of_nat (Nat.pow 2 order) - 6).
Proof.
  intro order. rewrite census_triple_slices.
  transitivity (census_triple_sum order (fun left middle right =>
    8 * (if thin_triple order left middle right then 1 else 0))).
  - unfold census_triple_sum. apply integer_cube_sum_ext. intro left.
    apply integer_cube_sum_ext. intro middle. apply integer_cube_sum_ext. intro right.
    rewrite census_top_bit_cancellation. destruct (thin_triple order left middle right); reflexivity.
  - rewrite census_triple_scale, census_thin_triple_count. reflexivity.
Qed.
Lemma census_triple_add : forall order first second,
  census_triple_sum order (fun left middle right => first left middle right + second left middle right) =
  census_triple_sum order first + census_triple_sum order second.
Proof.
  intros. unfold census_triple_sum.
  transitivity (integer_cube_sum order (fun left => integer_cube_sum order
    (fun middle => integer_cube_sum order (first left middle) + integer_cube_sum order (second left middle)))).
  - apply integer_cube_sum_ext. intro left. apply integer_cube_sum_ext. intro middle. apply integer_cube_sum_add.
  - transitivity (integer_cube_sum order (fun left =>
      integer_cube_sum order (fun middle => integer_cube_sum order (first left middle)) +
      integer_cube_sum order (fun middle => integer_cube_sum order (second left middle)))).
    + apply integer_cube_sum_ext. intro left. apply integer_cube_sum_add.
    + apply integer_cube_sum_add.
Qed.
Lemma census_triple_constant : forall order value,
  census_triple_sum order (fun _ _ _ => value) = Z.of_nat (Nat.pow 2 order) ^ 3 * value.
Proof.
  intros. unfold census_triple_sum.
  transitivity (integer_cube_sum order (fun _ => integer_cube_sum order
    (fun _ => Z.of_nat (Nat.pow 2 order) * value))).
  - apply integer_cube_sum_ext. intro left. apply integer_cube_sum_ext. intro middle. apply integer_cube_sum_constant.
  - transitivity (integer_cube_sum order (fun _ => Z.of_nat (Nat.pow 2 order) * (Z.of_nat (Nat.pow 2 order) * value))).
    + apply integer_cube_sum_ext. intro left. apply integer_cube_sum_constant.
    + rewrite integer_cube_sum_constant. ring.
Qed.
Definition associator_defect_count order : Z := census_triple_sum order
  (fun left middle right => if associator_phase order left middle right then 1 else 0).
Lemma census_phase_count_identity : forall order,
  census_triple_sum order (fun left middle right => phase_sign (associator_phase order left middle right)) =
  Z.of_nat (Nat.pow 2 order) ^ 3 - 2 * associator_defect_count order.
Proof.
  intro order. transitivity (census_triple_sum order (fun left middle right =>
    1 + (-2) * (if associator_phase order left middle right then 1 else 0))).
  - unfold census_triple_sum. apply integer_cube_sum_ext. intro left.
    apply integer_cube_sum_ext. intro middle. apply integer_cube_sum_ext. intro right.
    destruct (associator_phase order left middle right); reflexivity.
  - rewrite census_triple_add, census_triple_constant, census_triple_scale.
    unfold associator_defect_count. ring.
Qed.
Theorem associator_census_integrality : forall order,
  2 * associator_defect_count (S order) =
  (Z.of_nat (Nat.pow 2 (S order)) - 2) * (Z.of_nat (Nat.pow 2 (S order)) - 4) *
    (Z.of_nat (Nat.pow 2 (S order)) + 6).
Proof.
  intro order. pose proof (census_total_phase_sum order) as signed_sum.
  rewrite census_phase_count_identity in signed_sum.
  rewrite Nat.pow_succ_r', Nat2Z.inj_mul in *. cbn [Z.of_nat] in *. nia.
Qed.
Theorem associator_census_formula : forall order,
  associator_defect_count (S order) =
  ((Z.of_nat (Nat.pow 2 (S order)) - 2) * (Z.of_nat (Nat.pow 2 (S order)) - 4) *
    (Z.of_nat (Nat.pow 2 (S order)) + 6)) / 2.
Proof.
  intro order. rewrite <- associator_census_integrality.
  rewrite Z.mul_comm, Z.div_mul by discriminate. reflexivity.
Qed.
Print Assumptions census_top_bit_cancellation.
Print Assumptions census_thin_triple_count.
Print Assumptions associator_census_integrality.
Print Assumptions associator_census_formula.

Definition numeric_associator_defect_count order := census_triple_sum order
  (fun left middle right => if Z.eqb
    (numeric_associator_sign order order (cube_encode order left)
      (cube_encode order middle) (cube_encode order right)) (-1) then 1 else 0).
Example census_numeric_dimension_four : numeric_associator_defect_count 2 = 0.
Proof. vm_compute. reflexivity. Qed.
Example census_numeric_dimension_eight : numeric_associator_defect_count 3 = 168.
Proof. vm_compute. reflexivity. Qed.
Example census_numeric_dimension_sixteen : numeric_associator_defect_count 4 = 1848.
Proof. vm_compute. reflexivity. Qed.
Example census_numeric_dimension_thirty_two : numeric_associator_defect_count 5 = 15960.
Proof. vm_compute. reflexivity. Qed.

Lemma census_pair_symmetric : forall order (left right : cube order),
  pair_coefficient order left right = pair_coefficient order right left.
Proof. intros. unfold pair_coefficient. rewrite cube_xor_commutative. btauto. Qed.
Lemma census_sign_transpose : forall order (left right : cube order),
  sign_exponent order right left = xorb (sign_exponent order left right) (pair_coefficient order left right).
Proof.
  intros. pose proof (commutation_pair_coefficient order left right) as commutes.
  unfold commutation_phase in commutes. rewrite <- commutes. btauto.
Qed.
Lemma census_phase_zero_input : forall order (left middle : cube order),
  associator_phase order left middle (cube_zero order) = false.
Proof.
  intros. unfold associator_phase, schreier.
  rewrite (proj2 (sign_zero_left order middle)),
    (proj2 (sign_zero_left order (cube_xor order left middle))), cube_xor_zero. btauto.
Qed.
Lemma census_phase_left_input : forall order (left middle : cube order),
  associator_phase order left middle left = false.
Proof.
  intros. unfold associator_phase, schreier.
  rewrite (census_sign_transpose order left middle), (census_sign_transpose order left (cube_xor order left middle)),
    census_pair_translate, (cube_xor_commutative order middle left).
  btauto.
Qed.
Lemma census_phase_middle_input : forall order (left middle : cube order),
  associator_phase order left middle middle = false.
Proof.
  intros. unfold associator_phase, schreier. rewrite phase_cube_xor_self,
    (proj2 (sign_zero_left order left)), sign_diagonal,
    (census_sign_transpose order middle (cube_xor order left middle)),
    (census_sign_transpose order middle left),
    (cube_xor_commutative order left middle), census_pair_translate.
  pose proof (sign_row_involution order middle left) as inverse. rewrite <- inverse. btauto.
Qed.
Lemma census_phase_sum_input : forall order (left middle : cube order),
  associator_phase order left middle (cube_xor order left middle) = false.
Proof.
  intros. unfold associator_phase, schreier.
  rewrite (cube_xor_commutative order left middle), phase_cube_xor_involution,
    !sign_diagonal, (census_sign_transpose order middle left).
  pose proof (sign_row_involution order middle left) as inverse.
  unfold pair_coefficient. rewrite <- inverse. btauto.
Qed.
Definition dependent_basis_triple order (left middle right : cube order) : Prop :=
  left = cube_zero order \/ middle = cube_zero order \/ right = cube_zero order \/
  left = middle \/ left = right \/ middle = right \/ cube_xor order left middle = right.
Theorem dependent_basis_triple_associates : forall order (left middle right : cube order),
  dependent_basis_triple order left middle right -> associator_phase order left middle right = false.
Proof.
  intros order left middle right dependency. unfold dependent_basis_triple in dependency.
  destruct dependency as [zero|[zero|[zero|[equal|[equal|[equal|equal]]]]]].
  - subst left. apply (proj1 (degenerate_associator_zero order middle right)).
  - subst middle. apply (proj1 (proj2 (degenerate_associator_zero order left right))).
  - subst right. apply census_phase_zero_input.
  - subst middle. apply (proj2 (proj2 (degenerate_associator_zero order left right))).
  - subst right. apply census_phase_left_input.
  - subst right. apply census_phase_middle_input.
  - subst right. apply census_phase_sum_input.
Qed.
Print Assumptions dependent_basis_triple_associates.

Definition census_lifting_vector order (left middle right : cube order) : bool * bool * bool :=
  (pair_coefficient order middle right,
   xorb (pair_coefficient order left middle) (pair_coefficient order left (cube_xor order middle right)),
   pair_coefficient order left middle).
Theorem census_zero_relation_classes : forall order (left middle right : cube order),
  census_lifting_vector order (cube_zero order) middle right =
    (pair_coefficient order middle right, false, false) /\
  census_lifting_vector order left (cube_zero order) right =
    (false, pair_coefficient order left right, false) /\
  census_lifting_vector order left middle (cube_zero order) =
    (false, false, pair_coefficient order left middle).
Proof.
  intros. unfold census_lifting_vector. repeat split.
  - rewrite !census_pair_zero_left. reflexivity.
  - rewrite census_pair_zero_left, census_pair_zero_right,
      (cube_xor_commutative order (cube_zero order) right), cube_xor_zero. reflexivity.
  - rewrite !census_pair_zero_right, cube_xor_zero, xorb_nilpotent. reflexivity.
Qed.
Theorem census_repeated_relation_classes : forall order (left middle : cube order),
  census_lifting_vector order left left middle =
    (pair_coefficient order left middle, pair_coefficient order left middle, false) /\
  census_lifting_vector order left middle left =
    (pair_coefficient order left middle, false, pair_coefficient order left middle) /\
  census_lifting_vector order left middle middle =
    (false, pair_coefficient order left middle, pair_coefficient order left middle) /\
  census_lifting_vector order left middle (cube_xor order left middle) =
    (pair_coefficient order left middle, pair_coefficient order left middle, pair_coefficient order left middle).
Proof.
  intros. unfold census_lifting_vector. repeat split.
  - rewrite census_pair_diagonal, census_pair_translate. reflexivity.
  - rewrite (cube_xor_commutative order middle left), census_pair_translate,
      (census_pair_symmetric order middle left), xorb_nilpotent. reflexivity.
  - rewrite census_pair_diagonal, phase_cube_xor_self, census_pair_zero_right, xorb_false_r. reflexivity.
  - rewrite (cube_xor_commutative order left middle), phase_cube_xor_involution,
      census_pair_translate, census_pair_diagonal, (census_pair_symmetric order middle left), xorb_false_r. reflexivity.
Qed.
Theorem census_independent_relation_class : forall order (left middle right : cube order),
  ~ dependent_basis_triple order left middle right ->
  census_lifting_vector order left middle right = (true, false, true).
Proof.
  intros order left middle right independent.
  assert (nonzero : forall value : cube order, value <> cube_zero order -> cube_nonzero order value = true).
  { intros value distinct. unfold cube_nonzero. destruct (cube_equal order value (cube_zero order)) eqn:equal; [|reflexivity].
    apply cube_equal_spec in equal. contradiction. }
  assert (left_nonzero : cube_nonzero order left = true) by (apply nonzero; intro equal; apply independent; unfold dependent_basis_triple; tauto).
  assert (middle_nonzero : cube_nonzero order middle = true) by (apply nonzero; intro equal; apply independent; unfold dependent_basis_triple; tauto).
  assert (right_nonzero : cube_nonzero order right = true) by (apply nonzero; intro equal; apply independent; unfold dependent_basis_triple; tauto).
  assert (left_middle : left <> middle) by (intro equal; apply independent; unfold dependent_basis_triple; tauto).
  assert (middle_right : middle <> right) by (intro equal; apply independent; unfold dependent_basis_triple; tauto).
  assert (sum_nonzero : cube_nonzero order (cube_xor order middle right) = true) by (apply xor_nonzero_of_distinct; exact middle_right).
  assert (sum_distinct : left <> cube_xor order middle right).
  { intro equal. apply independent. unfold dependent_basis_triple. right; right; right; right; right; right.
    rewrite equal, cube_xor_commutative, phase_cube_xor_involution. reflexivity. }
  unfold census_lifting_vector. rewrite !independent_pair_coefficient by assumption. reflexivity.
Qed.
Theorem census_thin_relation_class : forall order (left middle right : cube order),
  thin_triple order left middle right = true <->
  census_lifting_vector order left middle right = (false, false, false).
Proof.
  intros. pose proof (census_top_coefficients order left middle right) as coefficients.
  unfold census_lifting_vector.
  destruct (pair_coefficient order left middle), (pair_coefficient order middle right),
    (pair_coefficient order left (cube_xor order middle right)); simpl in *; split; congruence.
Qed.
Print Assumptions census_zero_relation_classes.
Print Assumptions census_repeated_relation_classes.
Print Assumptions census_independent_relation_class.
Print Assumptions census_thin_relation_class.
