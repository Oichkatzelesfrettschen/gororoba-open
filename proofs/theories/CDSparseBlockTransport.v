(** Sparse CD support determines complete affine XOR sectors. *)
From Stdlib Require Import Arith Bool Lia Lra Reals List btauto.Btauto.
From OpenGororoba Require Import CDSignNumericCorrespondence SchreierSignCode CDAssociatorDoubling CDPhaseDegree CubeAffineCosets WalshProbability CDAssociatorCensus FiniteMatrixConventions CDSparseMatrixTransport RationalSignBlockRanks SparsePhotonicCertificates.
Local Open Scope R_scope.
Import divalg matrix mxalgebra rat.
Definition sparse_cd_entry order (operand : cube order -> R) (output input : cube order) :=
  operand (cube_xor order output input) * IZR (phase_sign
    (sign_exponent order (cube_xor order output input) input)).
Definition affine_supported order group (anchor : cube order) (vector : cube order -> R) :=
  forall input, same_coset order group input anchor = false -> vector input = 0.
Theorem sparse_cross_sector_zero : forall order group anchor operand output input,
  affine_supported order group anchor operand ->
  same_coset order group output (cube_xor order anchor input) = false ->
  sparse_cd_entry order operand output input = 0.
Proof.
  intros order group anchor operand output input supported cross.
  unfold sparse_cd_entry. rewrite supported; [ring|].
  unfold same_coset in *. rewrite <- cube_xor_associative, (cube_xor_commutative order input anchor). exact cross.
Qed.
Definition sparse_cd_apply order operand vector output :=
  real_cube_sum order (fun input => sparse_cd_entry order operand output input * vector input).
Lemma sparse_real_sum_zero : forall order, real_cube_sum order (fun _ => 0) = 0.
Proof. induction order; simpl; [reflexivity|rewrite IHorder; ring]. Qed.
Theorem sparse_support_transport : forall order group anchor seed operand vector,
  affine_supported order group anchor operand -> affine_supported order group seed vector ->
  affine_supported order group (cube_xor order anchor seed) (sparse_cd_apply order operand vector).
Proof.
  intros order group anchor seed operand vector operand_supported vector_supported output outside.
  unfold sparse_cd_apply. transitivity (real_cube_sum order (fun _ => 0)); [|].
  - apply real_cube_sum_ext. intro input.
    destruct (same_coset order group input seed) eqn:input_sector.
    + assert (cross : same_coset order group output (cube_xor order anchor input) = false).
      { destruct (same_coset order group output (cube_xor order anchor input)) eqn:inside; [|reflexivity].
        pose proof (same_coset_transitive order group output (cube_xor order anchor input)
          (cube_xor order anchor seed) inside) as translated.
        rewrite same_coset_translation in translated. specialize (translated input_sector).
        rewrite outside in translated. discriminate. }
      rewrite sparse_cross_sector_zero with (group := group) (anchor := anchor) by assumption. ring.
    + rewrite vector_supported by exact input_sector. ring.
  - apply sparse_real_sum_zero.
Qed.
Print Assumptions sparse_cross_sector_zero.
Print Assumptions sparse_support_transport.

Lemma sparse_real_sum_add : forall order first second,
  real_cube_sum order (fun input => first input + second input) =
  real_cube_sum order first + real_cube_sum order second.
Proof. induction order; intros; simpl; [reflexivity|]. rewrite !IHorder. ring. Qed.
Lemma sparse_real_sum_swap : forall first_order second_order function,
  real_cube_sum first_order (fun first => real_cube_sum second_order (function first)) =
  real_cube_sum second_order (fun second => real_cube_sum first_order (fun first => function first second)).
Proof.
  induction first_order; intros second_order function; [reflexivity|].
  change (real_cube_sum first_order (fun first => real_cube_sum second_order (function (first,false))) +
    real_cube_sum first_order (fun first => real_cube_sum second_order (function (first,true))) =
    real_cube_sum second_order (fun second =>
      real_cube_sum first_order (fun first => function (first,false) second) +
      real_cube_sum first_order (fun first => function (first,true) second))).
  rewrite !IHfirst_order, sparse_real_sum_add. reflexivity.
Qed.
Lemma sparse_real_delta_sum : forall order (target : cube order) amount,
  real_cube_sum order (fun input => if cube_equal order input target then amount else 0) = amount.
Proof.
  intros. transitivity (real_cube_sum order (fun input => amount * IZR (census_delta order target input))).
  - apply real_cube_sum_ext. intro input. unfold census_delta. destruct (cube_equal order input target); simpl; ring.
  - rewrite real_cube_sum_scale, real_cube_sum_IZR, census_delta_sum. simpl. ring.
Qed.
Definition sector_projection order group sector (vector : cube order -> R) input :=
  if same_coset order group input sector then vector input else 0.
Definition cube_squared_norm order (vector : cube order -> R) :=
  real_cube_sum order (fun input => vector input ^ 2).
Definition canonical_sector_squared_norm order group sector vector :=
  if cube_equal order (coset_representative order group sector) sector then
    cube_squared_norm order (sector_projection order group sector vector) else 0.
Theorem sparse_squared_norm_decomposition : forall order group vector,
  cube_squared_norm order vector =
  real_cube_sum order (fun sector => canonical_sector_squared_norm order group sector vector).
Proof.
  intros order group vector. symmetry.
  transitivity (real_cube_sum order (fun sector => real_cube_sum order (fun input =>
    if cube_equal order sector (coset_representative order group input) then vector input ^ 2 else 0))).
  - apply real_cube_sum_ext. intro sector. unfold canonical_sector_squared_norm, cube_squared_norm, sector_projection.
    transitivity (real_cube_sum order (fun input =>
      if andb (cube_equal order (coset_representative order group sector) sector)
        (same_coset order group input sector) then vector input ^ 2 else 0)).
    + destruct (cube_equal order (coset_representative order group sector) sector).
      * apply real_cube_sum_ext. intro input. destruct (same_coset order group input sector); simpl; ring.
      * symmetry. apply sparse_real_sum_zero.
    + apply real_cube_sum_ext. intro input. rewrite canonical_sector_gate. reflexivity.
  - rewrite sparse_real_sum_swap. unfold cube_squared_norm. apply real_cube_sum_ext. intro input. apply sparse_real_delta_sum.
Qed.
Print Assumptions sparse_squared_norm_decomposition.

Theorem sparse_block_intertwining : forall order group anchor sector operand vector output,
  affine_supported order group anchor operand ->
  sector_projection order group (cube_xor order anchor sector)
    (sparse_cd_apply order operand vector) output =
  sparse_cd_apply order operand (sector_projection order group sector vector) output.
Proof.
  intros order group anchor sector operand vector output supported.
  unfold sector_projection, sparse_cd_apply.
  transitivity (real_cube_sum order (fun input =>
    if same_coset order group output (cube_xor order anchor sector)
    then sparse_cd_entry order operand output input * vector input else 0)).
  { destruct (same_coset order group output (cube_xor order anchor sector)); [reflexivity|symmetry; apply sparse_real_sum_zero]. }
  apply real_cube_sum_ext. intro input.
  destruct (same_coset order group output (cube_xor order anchor input)) eqn:cross.
  - rewrite (same_coset_equivalent_left order group output (cube_xor order anchor input)
      (cube_xor order anchor sector) cross), same_coset_translation.
    destruct (same_coset order group input sector); ring.
  - rewrite sparse_cross_sector_zero with (group := group) (anchor := anchor) by assumption.
    destruct (same_coset order group output (cube_xor order anchor sector)),
      (same_coset order group input sector); ring.
Qed.
Theorem sparse_kernel_decomposition : forall order group anchor operand vector,
  affine_supported order group anchor operand ->
  (forall output, sparse_cd_apply order operand vector output = 0) <->
  (forall sector, coset_representative order group sector = sector ->
    forall output, sparse_cd_apply order operand (sector_projection order group sector vector) output = 0).
Proof.
  intros order group anchor operand vector supported. split.
  - intros kernel sector canonical output. rewrite <- sparse_block_intertwining with (anchor := anchor) by exact supported.
    unfold sector_projection. rewrite kernel. destruct (same_coset order group output (cube_xor order anchor sector)); reflexivity.
  - intros sectors output.
    specialize (sectors (coset_representative order group (cube_xor order anchor output))
      (coset_representative_idempotent order group (cube_xor order anchor output)) output).
    rewrite <- sparse_block_intertwining with (anchor := anchor) in sectors by exact supported.
    unfold sector_projection in sectors.
    assert (output_sector : same_coset order group output
      (cube_xor order anchor (coset_representative order group (cube_xor order anchor output))) = true).
    { pose proof (same_coset_translation order group anchor (cube_xor order anchor output)
        (coset_representative order group (cube_xor order anchor output))) as translation.
      rewrite phase_cube_xor_involution, coset_representative_member in translation. exact translation. }
    rewrite output_sector in sectors. exact sectors.
Qed.
Print Assumptions sparse_block_intertwining.
Print Assumptions sparse_kernel_decomposition.

Import ListNotations.
Definition sparse_sign_configuration order (left upper lower partner : cube order) sign_x sign_y :=
  ([phase_sign (sign_exponent order left lower);
    phase_sign (xorb sign_x (sign_exponent order upper partner));
    phase_sign (xorb sign_x (sign_exponent order upper lower));
    phase_sign (sign_exponent order left partner)], phase_sign sign_y).
Theorem sparse_photonic_configuration_coverage : forall order left upper lower partner sign_x sign_y,
  In (sparse_sign_configuration order left upper lower partner sign_x sign_y) retained_sparse_configurations.
Proof. intros. apply retained_sparse_configuration_coverage. Qed.
Theorem sparse_photonic_witness_coverage : forall order left upper lower partner sign_x sign_y,
  exists witness, In witness retained_sparse_witnesses /\
  photonic_witness_configuration witness = sparse_sign_configuration order left upper lower partner sign_x sign_y.
Proof. intros. apply retained_sparse_witness_total, sparse_photonic_configuration_coverage. Qed.
Definition two_label_output (first second third fourth input_sign : R) :=
  (first + input_sign * second, third + input_sign * fourth).
Definition photonic_label_output (first second third fourth input_sign : R) :=
  ((first / 2 + input_sign * (second / 2)) / sqrt 2,
   (third / 2 + input_sign * (fourth / 2)) / sqrt 2).
Definition two_label_squared_norm (output : R * R) := fst output ^ 2 + snd output ^ 2.
Theorem sparse_photonic_normalization : forall first second third fourth input_sign,
  two_label_squared_norm (photonic_label_output first second third fourth input_sign) =
  two_label_squared_norm (two_label_output first second third fourth input_sign) / 8.
Proof.
  intros. unfold two_label_squared_norm, photonic_label_output, two_label_output. cbn [fst snd].
  assert (square : sqrt 2 ^ 2 = 2) by (apply pow2_sqrt; lra).
  assert (nonzero : sqrt 2 <> 0) by (pose proof (sqrt_lt_R0 2); lra).
  unfold Rdiv. rewrite !Rpow_mult_distr, (pow_inv (sqrt 2) 2), square. field.
Qed.

Definition sparse_rational_sign_block order (left upper lower partner : cube order) sign_x :=
  rational_sign_block (sign_exponent order left lower)
    (xorb sign_x (sign_exponent order upper partner))
    (xorb sign_x (sign_exponent order upper lower)) (sign_exponent order left partner).
Theorem sparse_rational_sign_block_rank : forall order left upper lower partner sign_x,
  mxalgebra.mxrank (sparse_rational_sign_block order left upper lower partner sign_x) =
  if xorb (xorb (sign_exponent order left lower) (sign_exponent order upper partner))
    (xorb (sign_exponent order upper lower) (sign_exponent order left partner)) then 2%nat else 1%nat.
Proof.
  intros. unfold sparse_rational_sign_block. rewrite rational_sign_block_rank.
  assert (parity : xorb
    (xorb (sign_exponent order left lower) (xorb sign_x (sign_exponent order upper partner)))
    (xorb (xorb sign_x (sign_exponent order upper lower)) (sign_exponent order left partner)) =
    xorb (xorb (sign_exponent order left lower) (sign_exponent order upper partner))
      (xorb (sign_exponent order upper lower) (sign_exponent order left partner))) by btauto.
  rewrite parity. reflexivity.
Qed.
Definition cube_real_delta order (target input : cube order) : R :=
  if cube_equal order input target then 1 else 0.
Definition two_blade_vector order (lower upper : cube order) coefficient input :=
  cube_real_delta order lower input + coefficient * cube_real_delta order upper input.
Lemma sparse_weighted_delta_sum : forall order target function,
  real_cube_sum order (fun input => function input * cube_real_delta order target input) = function target.
Proof.
  intros. transitivity (real_cube_sum order (fun input =>
    if cube_equal order input target then function target else 0)).
  - apply real_cube_sum_ext. intro input. unfold cube_real_delta.
    destruct (cube_equal order input target) eqn:equal; [apply cube_equal_spec in equal; subst|]; ring.
  - apply sparse_real_delta_sum.
Qed.
Theorem sparse_two_blade_apply : forall order operand lower upper coefficient output,
  sparse_cd_apply order operand (two_blade_vector order lower upper coefficient) output =
  sparse_cd_entry order operand output lower + coefficient * sparse_cd_entry order operand output upper.
Proof.
  intros. unfold sparse_cd_apply, two_blade_vector.
  transitivity (real_cube_sum order (fun input =>
    sparse_cd_entry order operand output input * cube_real_delta order lower input +
    coefficient * (sparse_cd_entry order operand output input * cube_real_delta order upper input))).
  - apply real_cube_sum_ext. intro input. ring.
  - rewrite sparse_real_sum_add, real_cube_sum_scale, !sparse_weighted_delta_sum. ring.
Qed.
Lemma two_blade_lower_coordinate : forall order lower upper coefficient,
  lower <> upper -> two_blade_vector order lower upper coefficient lower = 1.
Proof.
  intros order lower upper coefficient distinct. unfold two_blade_vector, cube_real_delta.
  rewrite cube_equal_reflexive. destruct (cube_equal order lower upper) eqn:equal; [apply cube_equal_spec in equal; contradiction|ring].
Qed.
Lemma two_blade_upper_coordinate : forall order lower upper coefficient,
  lower <> upper -> two_blade_vector order lower upper coefficient upper = coefficient.
Proof.
  intros order lower upper coefficient distinct. unfold two_blade_vector, cube_real_delta.
  rewrite cube_equal_reflexive. destruct (cube_equal order upper lower) eqn:equal.
  - apply cube_equal_spec in equal. symmetry in equal. contradiction.
  - ring.
Qed.
Theorem sparse_two_label_output_coordinates : forall order (left upper lower partner : cube order) sign_x sign_y,
  left <> upper -> cube_xor order left upper = cube_xor order lower partner ->
  (sparse_cd_apply order (two_blade_vector order left upper sign_x)
    (two_blade_vector order lower partner sign_y) (cube_xor order left lower),
   sparse_cd_apply order (two_blade_vector order left upper sign_x)
    (two_blade_vector order lower partner sign_y) (cube_xor order left partner)) =
  two_label_output (IZR (phase_sign (sign_exponent order left lower)))
    (sign_x * IZR (phase_sign (sign_exponent order upper partner)))
    (sign_x * IZR (phase_sign (sign_exponent order upper lower)))
    (IZR (phase_sign (sign_exponent order left partner))) sign_y.
Proof.
  intros order left upper lower partner sign_x sign_y distinct same_label.
  assert (cross_lower : cube_xor order (cube_xor order left lower) partner = upper).
  { rewrite <- cube_xor_associative, <- same_label, phase_cube_xor_involution. reflexivity. }
  assert (cross_upper : cube_xor order (cube_xor order left partner) lower = upper).
  { rewrite <- cube_xor_associative, (cube_xor_commutative order partner lower), <- same_label, phase_cube_xor_involution. reflexivity. }
  rewrite !sparse_two_blade_apply. unfold sparse_cd_entry.
  rewrite !cube_xor_right_cancel, cross_lower, cross_upper,
    two_blade_lower_coordinate, two_blade_upper_coordinate by exact distinct.
  unfold two_label_output. f_equal; ring.
Qed.
Example photonic_bright_squared_norm : two_label_squared_norm (two_label_output 1 1 1 1 1) = 8.
Proof. unfold two_label_squared_norm, two_label_output. simpl. ring. Qed.
Example photonic_dark_squared_norm : two_label_squared_norm (two_label_output 1 1 1 1 (-1)) = 0.
Proof. unfold two_label_squared_norm, two_label_output. simpl. ring. Qed.
Example photonic_strut_probability : two_label_squared_norm (photonic_label_output 1 1 1 (-1) 1) = 1 / 2.
Proof. rewrite sparse_photonic_normalization. unfold two_label_squared_norm, two_label_output. simpl. field. Qed.
Print Assumptions sparse_rational_sign_block_rank.
Print Assumptions sparse_two_label_output_coordinates.
Print Assumptions sparse_photonic_normalization.

Theorem two_blade_affine_support : forall order lower upper coefficient,
  affine_supported order (pair_xor_subgroup order (cube_xor order lower upper)) lower
    (two_blade_vector order lower upper coefficient).
Proof.
  intros order lower upper coefficient input outside. unfold two_blade_vector, cube_real_delta.
  destruct (cube_equal order input lower) eqn:at_lower.
  { apply cube_equal_spec in at_lower. subst input. rewrite same_coset_reflexive in outside. discriminate. }
  destruct (cube_equal order input upper) eqn:at_upper.
  { apply cube_equal_spec in at_upper. subst input.
    pose proof (proj2 (pair_xor_coset_members order lower upper)) as member. rewrite member in outside. discriminate. }
  ring.
Qed.
Theorem two_blade_product_support : forall order (left upper lower partner : cube order) sign_x sign_y,
  cube_xor order left upper = cube_xor order lower partner ->
  affine_supported order (pair_xor_subgroup order (cube_xor order left upper)) (cube_xor order left lower)
    (sparse_cd_apply order (two_blade_vector order left upper sign_x) (two_blade_vector order lower partner sign_y)).
Proof.
  intros order left upper lower partner sign_x sign_y same_label. apply sparse_support_transport.
  - apply two_blade_affine_support.
  - rewrite same_label. apply two_blade_affine_support.
Qed.
Print Assumptions two_blade_affine_support.
Print Assumptions two_blade_product_support.

Lemma cube_two_point_squared_norm : forall order (first second : cube order) vector,
  first <> second ->
  (forall input, input <> first -> input <> second -> vector input = 0) ->
  cube_squared_norm order vector = vector first ^ 2 + vector second ^ 2.
Proof.
  intros order first second vector distinct supported. unfold cube_squared_norm.
  transitivity (real_cube_sum order (fun input =>
    (if cube_equal order input first then vector first ^ 2 else 0) +
    (if cube_equal order input second then vector second ^ 2 else 0))).
  - apply real_cube_sum_ext. intro input.
    destruct (cube_equal order input first) eqn:at_first,
      (cube_equal order input second) eqn:at_second.
    + apply cube_equal_spec in at_first, at_second. congruence.
    + apply cube_equal_spec in at_first. subst input. ring.
    + apply cube_equal_spec in at_second. subst input. ring.
    + assert (input <> first) by (intro equal; subst; rewrite cube_equal_reflexive in at_first; discriminate).
      assert (input <> second) by (intro equal; subst; rewrite cube_equal_reflexive in at_second; discriminate).
      rewrite supported by assumption. ring.
  - rewrite sparse_real_sum_add, !sparse_real_delta_sum. reflexivity.
Qed.
Lemma cube_xor_left_injective : forall order (anchor first second : cube order),
  cube_xor order anchor first = cube_xor order anchor second -> first = second.
Proof.
  intros order anchor first second equal.
  apply (f_equal (cube_xor order anchor)) in equal.
  rewrite !phase_cube_xor_involution in equal. exact equal.
Qed.
Lemma pair_coset_exact : forall order (first second input : cube order),
  same_coset order (pair_xor_subgroup order (cube_xor order first second)) input first = true ->
  input = first \/ input = second.
Proof.
  intros order first second input member. unfold same_coset in member.
  cbn [pair_xor_subgroup subgroup_member] in member. apply orb_true_iff in member.
  destruct member as [zero|equal]; apply cube_equal_spec in zero || apply cube_equal_spec in equal.
  - left. apply (f_equal (fun value => cube_xor order value first)) in zero.
    rewrite cube_xor_right_cancel, (cube_xor_commutative order (cube_zero order) first), cube_xor_zero in zero. exact zero.
  - right. rewrite (cube_xor_commutative order input first) in equal.
    apply cube_xor_left_injective in equal. exact equal.
Qed.
Theorem sparse_two_blade_full_squared_norm : forall order (left upper lower partner : cube order) sign_x sign_y,
  left <> upper -> cube_xor order left upper = cube_xor order lower partner ->
  cube_squared_norm order (sparse_cd_apply order (two_blade_vector order left upper sign_x)
    (two_blade_vector order lower partner sign_y)) =
  two_label_squared_norm (two_label_output (IZR (phase_sign (sign_exponent order left lower)))
    (sign_x * IZR (phase_sign (sign_exponent order upper partner)))
    (sign_x * IZR (phase_sign (sign_exponent order upper lower)))
    (IZR (phase_sign (sign_exponent order left partner))) sign_y).
Proof.
  intros order left upper lower partner sign_x sign_y distinct same_label.
  assert (inputs_distinct : lower <> partner).
  { intro equal. subst partner. rewrite phase_cube_xor_self in same_label.
    apply (f_equal (fun value => cube_xor order value upper)) in same_label.
    rewrite cube_xor_right_cancel, (cube_xor_commutative order (cube_zero order) upper), cube_xor_zero in same_label. contradiction. }
  rewrite (cube_two_point_squared_norm order (cube_xor order left lower) (cube_xor order left partner)).
  - pose proof (sparse_two_label_output_coordinates order left upper lower partner sign_x sign_y distinct same_label) as coordinates.
    apply (f_equal two_label_squared_norm) in coordinates. exact coordinates.
  - intro equal. apply cube_xor_left_injective in equal. contradiction.
  - intros input outside_first outside_second.
    apply (two_blade_product_support order left upper lower partner sign_x sign_y same_label).
    destruct (same_coset order (pair_xor_subgroup order (cube_xor order left upper)) input (cube_xor order left lower)) eqn:member; [|reflexivity].
    assert (label : cube_xor order (cube_xor order left lower) (cube_xor order left partner) = cube_xor order left upper).
    { rewrite cube_xor_four_swap, phase_cube_xor_self, (cube_xor_commutative order (cube_zero order) _), cube_xor_zero. symmetry. exact same_label. }
    rewrite <- label in member. apply pair_coset_exact in member. destruct member; contradiction.
Qed.
Print Assumptions sparse_two_blade_full_squared_norm.

Lemma cube_squared_norm_scale : forall order factor vector,
  cube_squared_norm order (fun input => factor * vector input) = factor ^ 2 * cube_squared_norm order vector.
Proof.
  intros. unfold cube_squared_norm. rewrite <- real_cube_sum_scale.
  apply real_cube_sum_ext. intro input. ring.
Qed.
Lemma sparse_cd_apply_scale : forall order left_scale right_scale operand vector output,
  sparse_cd_apply order (fun input => left_scale * operand input)
    (fun input => right_scale * vector input) output =
  (left_scale * right_scale) * sparse_cd_apply order operand vector output.
Proof.
  intros. unfold sparse_cd_apply, sparse_cd_entry. rewrite <- real_cube_sum_scale.
  apply real_cube_sum_ext. intro input. ring.
Qed.
Definition normalized_two_blade order lower upper coefficient input :=
  two_blade_vector order lower upper coefficient input / sqrt 2.
Theorem normalized_two_blade_unit_norm : forall order lower upper phase,
  lower <> upper -> cube_squared_norm order
    (normalized_two_blade order lower upper (IZR (phase_sign phase))) = 1.
Proof.
  intros order lower upper phase distinct. unfold normalized_two_blade.
  rewrite (cube_two_point_squared_norm order lower upper).
  - rewrite two_blade_lower_coordinate, two_blade_upper_coordinate by exact distinct.
    assert (square : sqrt 2 ^ 2 = 2) by (apply pow2_sqrt; lra).
    unfold Rdiv. rewrite !Rpow_mult_distr, (pow_inv (sqrt 2) 2), square.
    destruct phase; simpl; field.
  - exact distinct.
  - intros input outside_lower outside_upper. unfold two_blade_vector, cube_real_delta.
    destruct (cube_equal order input lower) eqn:at_lower,
      (cube_equal order input upper) eqn:at_upper; try (apply cube_equal_spec in at_lower; contradiction);
      try (apply cube_equal_spec in at_upper; contradiction); simpl; unfold Rdiv; ring.
Qed.
Theorem sparse_photonic_normalized_product : forall order (left upper lower partner : cube order) phase_x phase_y,
  left <> upper -> cube_xor order left upper = cube_xor order lower partner ->
  two_label_squared_norm (photonic_label_output
    (IZR (phase_sign (sign_exponent order left lower)))
    (IZR (phase_sign phase_x) * IZR (phase_sign (sign_exponent order upper partner)))
    (IZR (phase_sign phase_x) * IZR (phase_sign (sign_exponent order upper lower)))
    (IZR (phase_sign (sign_exponent order left partner))) (IZR (phase_sign phase_y))) =
  cube_squared_norm order (sparse_cd_apply order
    (normalized_two_blade order left upper (IZR (phase_sign phase_x)))
    (normalized_two_blade order lower partner (IZR (phase_sign phase_y)))) / 2.
Proof.
  intros order left upper lower partner phase_x phase_y distinct same_label.
  rewrite sparse_photonic_normalization.
  unfold normalized_two_blade, Rdiv.
  transitivity (cube_squared_norm order (sparse_cd_apply order
    (two_blade_vector order left upper (IZR (phase_sign phase_x)))
    (two_blade_vector order lower partner (IZR (phase_sign phase_y)))) / 8).
  - rewrite sparse_two_blade_full_squared_norm by assumption. reflexivity.
  - assert (square : sqrt 2 ^ 2 = 2) by (apply pow2_sqrt; lra).
    assert (pointwise : forall output,
      sparse_cd_apply order
        (fun input => two_blade_vector order left upper (IZR (phase_sign phase_x)) input * / sqrt 2)
        (fun input => two_blade_vector order lower partner (IZR (phase_sign phase_y)) input * / sqrt 2) output =
      (/2) * sparse_cd_apply order (two_blade_vector order left upper (IZR (phase_sign phase_x)))
        (two_blade_vector order lower partner (IZR (phase_sign phase_y))) output).
    { intro output.
      transitivity (sparse_cd_apply order
        (fun input => / sqrt 2 * two_blade_vector order left upper (IZR (phase_sign phase_x)) input)
        (fun input => / sqrt 2 * two_blade_vector order lower partner (IZR (phase_sign phase_y)) input) output).
      - unfold sparse_cd_apply, sparse_cd_entry. apply real_cube_sum_ext. intro input. ring.
      - rewrite sparse_cd_apply_scale.
        assert (inverse_square : / sqrt 2 * / sqrt 2 = /2).
        { rewrite <- Rinv_mult. replace (sqrt 2 * sqrt 2) with (sqrt 2 ^ 2) by ring. rewrite square. reflexivity. }
        rewrite inverse_square. reflexivity. }
    symmetry.
    transitivity (cube_squared_norm order (fun output => /2 * sparse_cd_apply order
      (two_blade_vector order left upper (IZR (phase_sign phase_x)))
      (two_blade_vector order lower partner (IZR (phase_sign phase_y))) output) * /2).
    + f_equal. unfold cube_squared_norm. apply real_cube_sum_ext. intro output.
      rewrite pointwise. reflexivity.
    + rewrite cube_squared_norm_scale. unfold Rdiv. field.
Qed.
Print Assumptions normalized_two_blade_unit_norm.
Print Assumptions sparse_photonic_normalized_product.

Import ssreflect.
Definition cube_matrix_index order (value : cube order) : fintype.ordinal (Nat.pow 2 order).
Proof. refine (@fintype.Ordinal (Nat.pow 2 order) (cube_encode order value) _). exact (ssrbool.introT ssrnat.ltP (cube_encode_bound order value)). Defined.
Definition two_blade_decoder order (first second : cube order) (index : fintype.ordinal 2) :=
  cube_matrix_index order (if Nat.eqb (fintype.nat_of_ord index) 0 then first else second).
Definition rational_two_blade order (left upper : cube order) phase input : rat.rat :=
  if cube_equal order input left then rational_phase_sign false
  else if cube_equal order input upper then rational_phase_sign phase else rat.ratz (ssrint.Posz 0).
Lemma rational_two_blade_left order left upper phase :
  rational_two_blade order left upper phase left = rational_phase_sign false.
Proof. unfold rational_two_blade. rw cube_equal_reflexive. reflexivity. Qed.
Lemma rational_two_blade_upper order left upper phase : left <> upper ->
  rational_two_blade order left upper phase upper = rational_phase_sign phase.
Proof.
  move=> distinct. unfold rational_two_blade. rw cube_equal_reflexive.
  destruct (cube_equal order upper left) eqn:equal; [apply cube_equal_spec in equal; congruence|reflexivity].
Qed.
Lemma rational_scalar_phase phase : @scalar_phase _ phase = rational_phase_sign phase.
Proof. destruct phase; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity. Qed.
Lemma rational_phase_product first second :
  rings_modules_and_algebras.GRing.mul (rational_phase_sign first) (rational_phase_sign second) =
  rational_phase_sign (xorb first second).
Proof. destruct first, second; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity. Qed.
Theorem sparse_two_blade_decoded_restriction order (left upper lower partner : cube order) phase :
  left <> upper -> cube_xor order left upper = cube_xor order lower partner ->
  matrix.mxsub
    (two_blade_decoder order (cube_xor order left lower) (cube_xor order left partner))
    (two_blade_decoder order lower partner)
    (@sparse_field_matrix _ order (rational_two_blade order left upper phase)) =
  sparse_rational_sign_block order left upper lower partner phase.
Proof.
  move=> distinct same_label.
  assert (cross_lower : cube_xor order (cube_xor order left lower) partner = upper).
  { rw -cube_xor_associative -same_label phase_cube_xor_involution. reflexivity. }
  assert (cross_upper : cube_xor order (cube_xor order left partner) lower = upper).
  { rw -cube_xor_associative (cube_xor_commutative order partner lower) -same_label phase_cube_xor_involution. reflexivity. }
  apply (proj1 (matrix.matrixP _ _)). intros row column.
  unfold sparse_rational_sign_block, rational_sign_block, sparse_field_matrix, two_blade_decoder.
  rw !matrix.mxE.
  case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord cube_matrix_index]; rw !cube_decode_encode;
    unfold sparse_field_entry;
    repeat first [progress rw cube_xor_right_cancel | progress rw cross_lower | progress rw cross_upper];
    repeat first [progress rw rational_two_blade_left | progress rw (rational_two_blade_upper _ _ _ _ distinct)];
    rw rational_scalar_phase rational_phase_product; reflexivity.
Qed.
Theorem sparse_two_blade_decoded_rank order (left upper lower partner : cube order) phase :
  left <> upper -> cube_xor order left upper = cube_xor order lower partner ->
  mxalgebra.mxrank (matrix.mxsub
    (two_blade_decoder order (cube_xor order left lower) (cube_xor order left partner))
    (two_blade_decoder order lower partner)
    (@sparse_field_matrix _ order (rational_two_blade order left upper phase))) =
  if xorb (xorb (sign_exponent order left lower) (sign_exponent order upper partner))
    (xorb (sign_exponent order upper lower) (sign_exponent order left partner)) then 2%nat else 1%nat.
Proof. move=> distinct label. rw (sparse_two_blade_decoded_restriction _ _ _ _ _ _ distinct label). apply sparse_rational_sign_block_rank. Qed.
Print Assumptions sparse_two_blade_decoded_restriction.
Print Assumptions sparse_two_blade_decoded_rank.
