(** Faithful average/detail coordinates retain both halves at every tower order. *)
From Stdlib Require Import Reals Lra.
From OpenGororoba Require Import RecursiveCDTower.
Local Open Scope R_scope.
Lemma tower_half_sum_reconstruction order : forall first second,
 tower_add order
 (tower_scale order (1/2) (tower_add order first second))
 (tower_scale order (1/2) (tower_sub order first second)) = first.
Proof.
 induction order as [|order induction_equal]; intros first second.
 - simpl; unfold tower_sub; simpl; field.
 - destruct first, second; simpl; unfold tower_sub in *; simpl.
   f_equal; apply induction_equal.
Qed.
Lemma tower_half_difference_reconstruction order : forall first second,
 tower_sub order
 (tower_scale order (1/2) (tower_add order first second))
 (tower_scale order (1/2) (tower_sub order first second)) = second.
Proof.
 induction order as [|order induction_equal]; intros first second.
 - unfold tower_sub; simpl; field.
 - destruct first, second; unfold tower_sub in *; simpl.
   f_equal; apply induction_equal.
Qed.
Lemma tower_average_reconstruction order : forall first second,
 tower_scale order (1/2) (tower_add order (tower_add order first second) (tower_sub order first second)) = first.
Proof.
 induction order as [|order induction_equal]; intros first second.
 - unfold tower_sub; simpl; field.
 - destruct first, second; unfold tower_sub in *; simpl.
   f_equal; apply induction_equal.
Qed.
Lemma tower_detail_reconstruction order : forall first second,
 tower_scale order (1/2) (tower_sub order (tower_add order first second) (tower_sub order first second)) = second.
Proof.
 induction order as [|order induction_equal]; intros first second.
 - unfold tower_sub; simpl; field.
 - destruct first, second; unfold tower_sub in *; simpl.
   f_equal; apply induction_equal.
Qed.
Definition tower_fold order (value : cd_tower (S order)) : cd_tower (S order) :=
 (tower_scale order (1/2) (tower_add order (fst value) (snd value)),
  tower_scale order (1/2) (tower_sub order (fst value) (snd value))).
Definition tower_unfold order (value : cd_tower (S order)) : cd_tower (S order) :=
 (tower_add order (fst value) (snd value),tower_sub order (fst value) (snd value)).
Theorem tower_unfold_after_fold order value : tower_unfold order (tower_fold order value) = value.
Proof.
 destruct value. unfold tower_unfold, tower_fold; simpl.
 rewrite tower_half_sum_reconstruction, tower_half_difference_reconstruction. reflexivity.
Qed.
Theorem tower_fold_after_unfold order value : tower_fold order (tower_unfold order value) = value.
Proof.
 destruct value. unfold tower_unfold, tower_fold; simpl.
 rewrite tower_average_reconstruction, tower_detail_reconstruction. reflexivity.
Qed.
Theorem tower_fold_injective order first second : tower_fold order first = tower_fold order second -> first = second.
Proof.
 intro equal. apply (f_equal (tower_unfold order)) in equal.
 rewrite !tower_unfold_after_fold in equal. exact equal.
Qed.
Theorem tower_fold_zero order : tower_fold order (tower_zero (S order)) = tower_zero (S order).
Proof.
 unfold tower_fold; simpl; unfold tower_sub.
 rewrite tower_neg_zero, !tower_add_zero, tower_scale_zero. reflexivity.
Qed.
Theorem tower_fold_eq_zero order value : tower_fold order value = tower_zero (S order) <-> value = tower_zero (S order).
Proof.
 split; intro equal.
 - apply (tower_fold_injective order value (tower_zero (S order))). rewrite equal, tower_fold_zero. reflexivity.
 - rewrite equal, tower_fold_zero. reflexivity.
Qed.
Definition tower_fold_product order first second :=
 tower_fold order (tower_mul (S order) (tower_unfold order first) (tower_unfold order second)).
Theorem tower_fold_product_correspondence order first second :
 tower_fold_product order (tower_fold order first) (tower_fold order second) = tower_fold order (tower_mul (S order) first second).
Proof. unfold tower_fold_product. rewrite !tower_unfold_after_fold. reflexivity. Qed.
Theorem tower_fold_zero_product order first second :
 tower_fold_product order first second = tower_zero (S order) <->
 tower_mul (S order) (tower_unfold order first) (tower_unfold order second) = tower_zero (S order).
Proof. unfold tower_fold_product. apply tower_fold_eq_zero. Qed.
Lemma tower_half_norm_identity order : forall first second,
 tower_norm_sq order (tower_scale order (1/2) (tower_add order first second)) +
 tower_norm_sq order (tower_scale order (1/2) (tower_sub order first second)) =
 (1/2) * (tower_norm_sq order first + tower_norm_sq order second).
Proof.
 induction order as [|order induction_equal]; intros first second.
 - unfold tower_sub; simpl; field.
 - destruct first as [first_low first_high], second as [second_low second_high].
   pose proof (induction_equal first_low second_low) as low_norm.
   pose proof (induction_equal first_high second_high) as high_norm.
   simpl; unfold tower_sub in *; simpl in *. nra.
Qed.
Theorem tower_fold_norm_scaling order value :
 tower_norm_sq (S order) (tower_fold order value) = 2 * tower_norm_sq (S order) value.
Proof. destruct value; unfold tower_fold; simpl. apply tower_half_norm_identity. Qed.
Theorem tower_unfold_norm_scaling order value :
 tower_norm_sq (S order) (tower_unfold order value) = 2 * tower_norm_sq (S order) value.
Proof.
 pose proof (tower_fold_norm_scaling order (tower_unfold order value)) as scale.
 rewrite tower_fold_after_unfold in scale. lra.
Qed.
Print Assumptions tower_unfold_after_fold.
Print Assumptions tower_fold_after_unfold.
Print Assumptions tower_fold_zero_product.
Print Assumptions tower_fold_norm_scaling.
