(** * Faithful average/detail coordinates for the concrete 16D sedenions.

    The transform retains two octonions: the half-sum and half-difference
    of the original octonion halves. Reconstruction recovers all 16 real
    coordinates. Multiplication transported through the inverse transform
    preserves and reflects zero products.

    Multiplying only the octonion averages uses a different multiplication
    law on eight coordinates. The explicit pair [sed_zd_a], [sed_zd_b] has
    sedenion product zero, while its octonion average product is [oct_e 5]/2.

    Every theorem uses the concrete [CDSed] and [sed_mul] convention from
    [Sedenion]. The 16D inverse laws instantiate the all-order transport through
    the proved recursive-tower and concrete-record correspondence. *)

From OpenGororoba Require Import
  Prelude CayleyDicksonAlgebra Sedenion OctonionNorm.
From OpenGororoba Require Import RecursiveCDTower CDTowerFoldTransport CDConcreteTowerAdapter.

Open Scope R_scope.

Definition sed_average (value : CDSed) : CDOct :=
  oct_scale (1 / 2) (oct_add (sed_lo value) (sed_hi value)).

Definition sed_detail (value : CDSed) : CDOct :=
  oct_scale (1 / 2) (oct_sub (sed_lo value) (sed_hi value)).

(** Both octonions remain present in the coordinate representation. *)
Definition sed_fold (value : CDSed) : CDSed :=
  mkSed (sed_average value) (sed_detail value).

Definition sed_unfold (coordinates : CDSed) : CDSed :=
  mkSed
    (oct_add (sed_lo coordinates) (sed_hi coordinates))
    (oct_sub (sed_lo coordinates) (sed_hi coordinates)).

Lemma tower_sedenion_fold_correspondence value :
 tower_sedenion (tower_fold 3 value) = sed_fold (tower_sedenion value).
Proof.
 destruct value as [low high].
 change (mkSed
   (tower_octonion (tower_scale 3 (1/2) (tower_add 3 low high)))
   (tower_octonion (tower_scale 3 (1/2) (tower_sub 3 low high))) =
   mkSed (oct_scale (1/2) (oct_add (tower_octonion low) (tower_octonion high)))
   (oct_scale (1/2) (oct_sub (tower_octonion low) (tower_octonion high)))).
 rewrite !tower_octonion_scale, tower_octonion_add.
 unfold tower_sub, oct_sub. rewrite tower_octonion_add, tower_octonion_neg. reflexivity.
Qed.
Lemma tower_sedenion_unfold_correspondence value :
 tower_sedenion (tower_unfold 3 value) = sed_unfold (tower_sedenion value).
Proof.
 destruct value as [low high].
 change (mkSed (tower_octonion (tower_add 3 low high)) (tower_octonion (tower_sub 3 low high)) =
   mkSed (oct_add (tower_octonion low) (tower_octonion high)) (oct_sub (tower_octonion low) (tower_octonion high))).
 unfold tower_sub, oct_sub. rewrite !tower_octonion_add, tower_octonion_neg. reflexivity.
Qed.

Theorem sed_unfold_after_fold :
  forall value, sed_unfold (sed_fold value) = value.
Proof.
  intro value.
  pose proof (f_equal tower_sedenion (tower_unfold_after_fold 3 (sedenion_tower value))) as transported.
  rewrite tower_sedenion_unfold_correspondence, tower_sedenion_fold_correspondence,
    tower_sedenion_round_trip in transported. exact transported.
Qed.

Theorem sed_fold_after_unfold :
  forall coordinates, sed_fold (sed_unfold coordinates) = coordinates.
Proof.
  intro coordinates.
  pose proof (f_equal tower_sedenion (tower_fold_after_unfold 3 (sedenion_tower coordinates))) as transported.
  rewrite tower_sedenion_fold_correspondence, tower_sedenion_unfold_correspondence,
    tower_sedenion_round_trip in transported. exact transported.
Qed.

Theorem sed_fold_injective :
  forall left right, sed_fold left = sed_fold right -> left = right.
Proof.
  intros left right same_coordinates.
  rewrite <- (sed_unfold_after_fold left).
  rewrite <- (sed_unfold_after_fold right).
  now rewrite same_coordinates.
Qed.

Lemma sed_fold_zero : sed_fold sed_zero = sed_zero.
Proof.
  cbv [sed_fold sed_average sed_detail sed_zero oct_zero quat_zero
       oct_add oct_sub oct_neg oct_scale quat_add quat_neg quat_scale
       sed_lo sed_hi oct_lo oct_hi qa qb qc qd].
  f_equal; f_equal; f_equal; field.
Qed.

(** Transport reconstructs the original factors before multiplication and
    expresses the resulting sedenion in average/detail coordinates. *)
Definition sed_fold_product (left right : CDSed) : CDSed :=
  sed_fold (sed_mul (sed_unfold left) (sed_unfold right)).

Theorem sed_fold_product_transport :
  forall left right,
    sed_fold_product (sed_fold left) (sed_fold right) =
      sed_fold (sed_mul left right).
Proof.
  intros left right.
  unfold sed_fold_product.
  now rewrite !sed_unfold_after_fold.
Qed.

Theorem sed_fold_product_zero_iff :
  forall left right,
    sed_fold_product left right = sed_zero <->
      sed_mul (sed_unfold left) (sed_unfold right) = sed_zero.
Proof.
  intros left right.
  unfold sed_fold_product.
  split.
  - intros folded_product_zero.
    apply sed_fold_injective.
    rewrite sed_fold_zero.
    exact folded_product_zero.
  - intros original_product_zero.
    rewrite original_product_zero.
    exact sed_fold_zero.
Qed.

Theorem sed_fold_preserves_and_reflects_zero_product :
  forall left right,
    sed_fold_product (sed_fold left) (sed_fold right) = sed_zero <->
      sed_mul left right = sed_zero.
Proof.
  intros left right.
  rewrite sed_fold_product_zero_iff.
  now rewrite !sed_unfold_after_fold.
Qed.

Theorem sed_fold_witness_product_zero :
  sed_fold_product (sed_fold sed_zd_a) (sed_fold sed_zd_b) = sed_zero.
Proof.
  apply sed_fold_preserves_and_reflects_zero_product.
  exact sed_zd_product_zero.
Qed.

(** The octonion averages discard the detail coordinates of the original
    zero-divisor pair [e3 + e10], [e6 - e15]. *)
Theorem sed_average_witness_product :
  oct_mul (sed_average sed_zd_a) (sed_average sed_zd_b) =
    oct_scale (1 / 2) (oct_e 5).
Proof.
  cbv [sed_average sed_zd_a sed_zd_b oct_add oct_scale oct_e oct_mul
       quat_mul quat_add quat_neg quat_conj quat_scale quat_zero quat_one
       sed_lo sed_hi oct_lo oct_hi qa qb qc qd].
  f_equal; f_equal; field.
Qed.

Theorem sed_average_witness_product_nonzero :
  oct_mul (sed_average sed_zd_a) (sed_average sed_zd_b) <> oct_zero.
Proof.
  rewrite sed_average_witness_product.
  intros average_product_zero.
  pose proof (f_equal (fun value => qb (oct_hi value)) average_product_zero)
    as nonzero_coordinate.
  cbv [oct_scale oct_e oct_zero quat_scale quat_zero quat_one
       oct_hi qb] in nonzero_coordinate.
  lra.
Qed.

Theorem sed_average_loses_zero_product :
  exists left right : CDSed,
    sed_mul left right = sed_zero /\
    oct_mul (sed_average left) (sed_average right) <> oct_zero.
Proof.
  exists sed_zd_a, sed_zd_b.
  split.
  - exact sed_zd_product_zero.
  - exact sed_average_witness_product_nonzero.
Qed.
Theorem sed_fold_norm_scaling value :
 sed_norm_sq (sed_fold value) = (1/2) * sed_norm_sq value.
Proof.
 pose proof (tower_fold_norm_scaling 3 (sedenion_tower value)) as transported.
 rewrite !tower_sedenion_norm, tower_sedenion_fold_correspondence,
   tower_sedenion_round_trip in transported. exact transported.
Qed.
Theorem sed_unfold_norm_scaling value :
 sed_norm_sq (sed_unfold value) = 2 * sed_norm_sq value.
Proof.
 pose proof (tower_unfold_norm_scaling 3 (sedenion_tower value)) as transported.
 rewrite !tower_sedenion_norm, tower_sedenion_unfold_correspondence,
   tower_sedenion_round_trip in transported. exact transported.
Qed.
Lemma tower_sedenion_average_correspondence value :
 tower_octonion (fst (tower_fold 3 value)) = sed_average (tower_sedenion value).
Proof. exact (f_equal sed_lo (tower_sedenion_fold_correspondence value)). Qed.
Theorem tower_average_loses_zero_product :
 exists first second : cd_tower 4,
 tower_mul 4 first second = tower_zero 4 /\
 tower_mul 3 (fst (tower_fold 3 first)) (fst (tower_fold 3 second)) <> tower_zero 3.
Proof.
 exists (sedenion_tower sed_zd_a), (sedenion_tower sed_zd_b). split.
 - apply tower_sedenion_injective.
   rewrite tower_sedenion_mul, !tower_sedenion_round_trip, tower_sedenion_zero.
   exact sed_zd_product_zero.
 - intro equal. apply (f_equal tower_octonion) in equal.
   rewrite tower_octonion_mul, !tower_sedenion_average_correspondence,
     !tower_sedenion_round_trip, tower_octonion_zero in equal.
   exact (sed_average_witness_product_nonzero equal).
Qed.
Print Assumptions sed_unfold_after_fold.
Print Assumptions sed_fold_after_unfold.
Print Assumptions sed_fold_norm_scaling.
Print Assumptions tower_average_loses_zero_product.
