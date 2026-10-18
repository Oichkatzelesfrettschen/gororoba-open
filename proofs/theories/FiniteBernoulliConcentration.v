(** Concentration from the finite IID Bernoulli convolution law. *)
From Stdlib Require Import Reals List Lra Psatz Lia.
From OpenGororoba Require Import FiniteProbability.
Import ListNotations.
Open Scope R_scope.

Fixpoint bernoulli_expectation (samples : nat) (parameter : R) (observable : R -> R) : R :=
  match samples with
  | O => observable 0
  | S previous =>
      (1 - parameter) * bernoulli_expectation previous parameter (fun centered => observable (centered - parameter)) +
      parameter * bernoulli_expectation previous parameter (fun centered => observable (centered + (1 - parameter)))
  end.
Lemma bernoulli_expectation_ext samples parameter f g :
  (forall centered, f centered = g centered) ->
  bernoulli_expectation samples parameter f = bernoulli_expectation samples parameter g.
Proof. revert f g; induction samples; intros f g Heq; simpl; [apply Heq|].
  rewrite (IHsamples _ _ (fun centered => Heq (centered - parameter))).
  rewrite (IHsamples _ _ (fun centered => Heq (centered + (1 - parameter)))); reflexivity. Qed.
Lemma bernoulli_expectation_add samples parameter f g :
  bernoulli_expectation samples parameter (fun centered => f centered + g centered) =
  bernoulli_expectation samples parameter f + bernoulli_expectation samples parameter g.
Proof. revert f g; induction samples; intros f g; simpl; [ring|].
  rewrite !IHsamples; ring. Qed.
Lemma bernoulli_expectation_scale samples parameter scalar f :
  bernoulli_expectation samples parameter (fun centered => scalar * f centered) =
  scalar * bernoulli_expectation samples parameter f.
Proof. revert f; induction samples; intros f; simpl; [ring|].
  rewrite !IHsamples; ring. Qed.
Lemma bernoulli_expectation_one samples parameter :
  bernoulli_expectation samples parameter (fun _ => 1) = 1.
Proof. induction samples; simpl; [ring|rewrite IHsamples; ring]. Qed.
Lemma bernoulli_expectation_step samples parameter f :
  bernoulli_expectation (S samples) parameter f =
  bernoulli_expectation samples parameter
    (fun centered => (1-parameter)*f(centered-parameter)+parameter*f(centered+(1-parameter))).
Proof. simpl; rewrite bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity. Qed.
Definition centered_moment samples parameter degree :=
  bernoulli_expectation samples parameter (fun centered => centered ^ degree).
Definition increment_moment parameter degree :=
  (1-parameter)*(-parameter)^degree + parameter*(1-parameter)^degree.

Lemma unit_power_bound value degree :
  0 <= value <= 1 -> 0 <= value ^ degree <= 1.
Proof. intros Hvalue; split; [apply pow_le; lra|].
  pose proof (pow_incr value 1 degree Hvalue); rewrite pow1 in H; exact H. Qed.
Lemma unit_power_square_bound value degree :
  0 <= value <= 1 -> (2 <= degree)%nat -> value ^ degree <= value ^ 2.
Proof. intros Hvalue Hdegree.
  replace degree with (2 + (degree-2))%nat by lia.
  rewrite pow_add.
  pose proof (unit_power_bound value (degree-2) Hvalue).
  pose proof (pow_le value 2 (proj1 Hvalue)); nra. Qed.
Lemma increment_moment_bound parameter degree :
  0 <= parameter <= 1 -> (2 <= degree)%nat ->
  Rabs (increment_moment parameter degree) <= 1/4.
Proof.
  intros Hparameter Hdegree; unfold increment_moment.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite !Rabs_mult, <- !RPow_abs.
  rewrite Rabs_Ropp, (Rabs_right (1-parameter)), (Rabs_right parameter) by lra.
  pose proof (unit_power_square_bound parameter degree Hparameter Hdegree).
  assert (Hcomplement : 0 <= 1-parameter <= 1) by lra.
  pose proof (unit_power_square_bound (1-parameter) degree Hcomplement Hdegree).
  pose proof (Rle_0_sqr (parameter-1/2)) as Hsquare.
  assert (Hvariance : parameter*(1-parameter) <= 1/4) by (unfold Rsqr in Hsquare; nra).
  simpl in *; nra.
Qed.
Lemma absolute_moment_term scalar increment moment bound :
  0 <= scalar -> Rabs increment <= 1/4 -> Rabs moment <= bound ->
  Rabs (scalar * increment * moment) <= scalar * bound / 4.
Proof. intros Hscalar Hincrement Hmoment.
  rewrite !Rabs_mult, (Rabs_right scalar) by lra.
  pose proof (Rabs_pos increment); pose proof (Rabs_pos moment).
  assert (0 <= bound) by lra.
  assert (Rabs increment * Rabs moment <= bound/4) by nra.
  nra.
Qed.

Definition moment_envelope (degree : nat) (count : R) : R :=
match degree with
| 0%nat => 1
| 1%nat => 0
| 2%nat => (1 * count ^ 1 / 4)
| 3%nat => (1 * count ^ 1 / 4)
| 4%nat => (1 * count ^ 1 / 4) + (3 * count ^ 2 / 16)
| 5%nat => (1 * count ^ 1 / 4) + (10 * count ^ 2 / 16)
| 6%nat => (1 * count ^ 1 / 4) + (25 * count ^ 2 / 16) + (15 * count ^ 3 / 64)
| 7%nat => (1 * count ^ 1 / 4) + (56 * count ^ 2 / 16) + (105 * count ^ 3 / 64)
| 8%nat => (1 * count ^ 1 / 4) + (119 * count ^ 2 / 16) + (490 * count ^ 3 / 64) + (105 * count ^ 4 / 256)
| 9%nat => (1 * count ^ 1 / 4) + (246 * count ^ 2 / 16) + (1918 * count ^ 3 / 64) + (1260 * count ^ 4 / 256)
| 10%nat => (1 * count ^ 1 / 4) + (501 * count ^ 2 / 16) + (6825 * count ^ 3 / 64) + (9450 * count ^ 4 / 256) + (945 * count ^ 5 / 1024)
| _ => 0
end.

Lemma centered_moment_recurrence_2 samples parameter :
centered_moment (S samples) parameter 2 =
centered_moment samples parameter 2 + (1 * increment_moment parameter 2 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 2 + (1 * increment_moment parameter 2 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_2 count :
0 <= count ->
moment_envelope 2 count + (1 * moment_envelope 0 count / 4)
<= moment_envelope 2 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.

Lemma centered_moment_recurrence_3 samples parameter :
centered_moment (S samples) parameter 3 =
centered_moment samples parameter 3 + (3 * increment_moment parameter 2 * centered_moment samples parameter 1) + (1 * increment_moment parameter 3 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 3 + (3 * increment_moment parameter 2 * centered ^ 1) + (1 * increment_moment parameter 3 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_3 count :
0 <= count ->
moment_envelope 3 count + (3 * moment_envelope 1 count / 4) + (1 * moment_envelope 0 count / 4)
<= moment_envelope 3 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.

Lemma centered_moment_recurrence_4 samples parameter :
centered_moment (S samples) parameter 4 =
centered_moment samples parameter 4 + (6 * increment_moment parameter 2 * centered_moment samples parameter 2) + (4 * increment_moment parameter 3 * centered_moment samples parameter 1) + (1 * increment_moment parameter 4 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 4 + (6 * increment_moment parameter 2 * centered ^ 2) + (4 * increment_moment parameter 3 * centered ^ 1) + (1 * increment_moment parameter 4 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_4 count :
0 <= count ->
moment_envelope 4 count + (6 * moment_envelope 2 count / 4) + (4 * moment_envelope 1 count / 4) + (1 * moment_envelope 0 count / 4)
<= moment_envelope 4 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.

Lemma centered_moment_recurrence_5 samples parameter :
centered_moment (S samples) parameter 5 =
centered_moment samples parameter 5 + (10 * increment_moment parameter 2 * centered_moment samples parameter 3) + (10 * increment_moment parameter 3 * centered_moment samples parameter 2) + (5 * increment_moment parameter 4 * centered_moment samples parameter 1) + (1 * increment_moment parameter 5 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 5 + (10 * increment_moment parameter 2 * centered ^ 3) + (10 * increment_moment parameter 3 * centered ^ 2) + (5 * increment_moment parameter 4 * centered ^ 1) + (1 * increment_moment parameter 5 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_5 count :
0 <= count ->
moment_envelope 5 count + (10 * moment_envelope 3 count / 4) + (10 * moment_envelope 2 count / 4) + (5 * moment_envelope 1 count / 4) + (1 * moment_envelope 0 count / 4)
<= moment_envelope 5 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.

Lemma centered_moment_recurrence_6 samples parameter :
centered_moment (S samples) parameter 6 =
centered_moment samples parameter 6 + (15 * increment_moment parameter 2 * centered_moment samples parameter 4) + (20 * increment_moment parameter 3 * centered_moment samples parameter 3) + (15 * increment_moment parameter 4 * centered_moment samples parameter 2) + (6 * increment_moment parameter 5 * centered_moment samples parameter 1) + (1 * increment_moment parameter 6 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 6 + (15 * increment_moment parameter 2 * centered ^ 4) + (20 * increment_moment parameter 3 * centered ^ 3) + (15 * increment_moment parameter 4 * centered ^ 2) + (6 * increment_moment parameter 5 * centered ^ 1) + (1 * increment_moment parameter 6 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_6 count :
0 <= count ->
moment_envelope 6 count + (15 * moment_envelope 4 count / 4) + (20 * moment_envelope 3 count / 4) + (15 * moment_envelope 2 count / 4) + (6 * moment_envelope 1 count / 4) + (1 * moment_envelope 0 count / 4)
<= moment_envelope 6 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.

Lemma centered_moment_recurrence_7 samples parameter :
centered_moment (S samples) parameter 7 =
centered_moment samples parameter 7 + (21 * increment_moment parameter 2 * centered_moment samples parameter 5) + (35 * increment_moment parameter 3 * centered_moment samples parameter 4) + (35 * increment_moment parameter 4 * centered_moment samples parameter 3) + (21 * increment_moment parameter 5 * centered_moment samples parameter 2) + (7 * increment_moment parameter 6 * centered_moment samples parameter 1) + (1 * increment_moment parameter 7 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 7 + (21 * increment_moment parameter 2 * centered ^ 5) + (35 * increment_moment parameter 3 * centered ^ 4) + (35 * increment_moment parameter 4 * centered ^ 3) + (21 * increment_moment parameter 5 * centered ^ 2) + (7 * increment_moment parameter 6 * centered ^ 1) + (1 * increment_moment parameter 7 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_7 count :
0 <= count ->
moment_envelope 7 count + (21 * moment_envelope 5 count / 4) + (35 * moment_envelope 4 count / 4) + (35 * moment_envelope 3 count / 4) + (21 * moment_envelope 2 count / 4) + (7 * moment_envelope 1 count / 4) + (1 * moment_envelope 0 count / 4)
<= moment_envelope 7 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.

Lemma centered_moment_recurrence_8 samples parameter :
centered_moment (S samples) parameter 8 =
centered_moment samples parameter 8 + (28 * increment_moment parameter 2 * centered_moment samples parameter 6) + (56 * increment_moment parameter 3 * centered_moment samples parameter 5) + (70 * increment_moment parameter 4 * centered_moment samples parameter 4) + (56 * increment_moment parameter 5 * centered_moment samples parameter 3) + (28 * increment_moment parameter 6 * centered_moment samples parameter 2) + (8 * increment_moment parameter 7 * centered_moment samples parameter 1) + (1 * increment_moment parameter 8 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 8 + (28 * increment_moment parameter 2 * centered ^ 6) + (56 * increment_moment parameter 3 * centered ^ 5) + (70 * increment_moment parameter 4 * centered ^ 4) + (56 * increment_moment parameter 5 * centered ^ 3) + (28 * increment_moment parameter 6 * centered ^ 2) + (8 * increment_moment parameter 7 * centered ^ 1) + (1 * increment_moment parameter 8 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_8 count :
0 <= count ->
moment_envelope 8 count + (28 * moment_envelope 6 count / 4) + (56 * moment_envelope 5 count / 4) + (70 * moment_envelope 4 count / 4) + (56 * moment_envelope 3 count / 4) + (28 * moment_envelope 2 count / 4) + (8 * moment_envelope 1 count / 4) + (1 * moment_envelope 0 count / 4)
<= moment_envelope 8 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.

Lemma centered_moment_recurrence_9 samples parameter :
centered_moment (S samples) parameter 9 =
centered_moment samples parameter 9 + (36 * increment_moment parameter 2 * centered_moment samples parameter 7) + (84 * increment_moment parameter 3 * centered_moment samples parameter 6) + (126 * increment_moment parameter 4 * centered_moment samples parameter 5) + (126 * increment_moment parameter 5 * centered_moment samples parameter 4) + (84 * increment_moment parameter 6 * centered_moment samples parameter 3) + (36 * increment_moment parameter 7 * centered_moment samples parameter 2) + (9 * increment_moment parameter 8 * centered_moment samples parameter 1) + (1 * increment_moment parameter 9 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 9 + (36 * increment_moment parameter 2 * centered ^ 7) + (84 * increment_moment parameter 3 * centered ^ 6) + (126 * increment_moment parameter 4 * centered ^ 5) + (126 * increment_moment parameter 5 * centered ^ 4) + (84 * increment_moment parameter 6 * centered ^ 3) + (36 * increment_moment parameter 7 * centered ^ 2) + (9 * increment_moment parameter 8 * centered ^ 1) + (1 * increment_moment parameter 9 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_9 count :
0 <= count ->
moment_envelope 9 count + (36 * moment_envelope 7 count / 4) + (84 * moment_envelope 6 count / 4) + (126 * moment_envelope 5 count / 4) + (126 * moment_envelope 4 count / 4) + (84 * moment_envelope 3 count / 4) + (36 * moment_envelope 2 count / 4) + (9 * moment_envelope 1 count / 4) + (1 * moment_envelope 0 count / 4)
<= moment_envelope 9 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.

Lemma centered_moment_recurrence_10 samples parameter :
centered_moment (S samples) parameter 10 =
centered_moment samples parameter 10 + (45 * increment_moment parameter 2 * centered_moment samples parameter 8) + (120 * increment_moment parameter 3 * centered_moment samples parameter 7) + (210 * increment_moment parameter 4 * centered_moment samples parameter 6) + (252 * increment_moment parameter 5 * centered_moment samples parameter 5) + (210 * increment_moment parameter 6 * centered_moment samples parameter 4) + (120 * increment_moment parameter 7 * centered_moment samples parameter 3) + (45 * increment_moment parameter 8 * centered_moment samples parameter 2) + (10 * increment_moment parameter 9 * centered_moment samples parameter 1) + (1 * increment_moment parameter 10 * centered_moment samples parameter 0).
Proof.
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered =>
centered ^ 10 + (45 * increment_moment parameter 2 * centered ^ 8) + (120 * increment_moment parameter 3 * centered ^ 7) + (210 * increment_moment parameter 4 * centered ^ 6) + (252 * increment_moment parameter 5 * centered ^ 5) + (210 * increment_moment parameter 6 * centered ^ 4) + (120 * increment_moment parameter 7 * centered ^ 3) + (45 * increment_moment parameter 8 * centered ^ 2) + (10 * increment_moment parameter 9 * centered ^ 1) + (1 * increment_moment parameter 10 * centered ^ 0))).
{ apply bernoulli_expectation_ext; intros centered; unfold increment_moment; simpl; ring. }
rewrite !bernoulli_expectation_add, !bernoulli_expectation_scale; reflexivity.
Qed.

Lemma moment_envelope_step_10 count :
0 <= count ->
moment_envelope 10 count + (45 * moment_envelope 8 count / 4) + (120 * moment_envelope 7 count / 4) + (210 * moment_envelope 6 count / 4) + (252 * moment_envelope 5 count / 4) + (210 * moment_envelope 4 count / 4) + (120 * moment_envelope 3 count / 4) + (45 * moment_envelope 2 count / 4) + (10 * moment_envelope 1 count / 4) + (1 * moment_envelope 0 count / 4)
<= moment_envelope 10 (count+1).
Proof. intros Hcount; unfold moment_envelope.
pose proof (pow_le count 1 Hcount) as Hpower1;
pose proof (pow_le count 2 Hcount) as Hpower2;
pose proof (pow_le count 3 Hcount) as Hpower3;
pose proof (pow_le count 4 Hcount) as Hpower4;
pose proof (pow_le count 5 Hcount) as Hpower5;
simpl in *; nra.
Qed.


Lemma absolute_add_bound left right left_bound right_bound :
Rabs left <= left_bound -> Rabs right <= right_bound ->
Rabs (left+right) <= left_bound+right_bound.
Proof. intros Hleft Hright; eapply Rle_trans; [apply Rabs_triang|lra]. Qed.
Lemma centered_moment_zero samples parameter :
centered_moment samples parameter 0 = 1.
Proof. unfold centered_moment; apply bernoulli_expectation_one. Qed.
Lemma centered_moment_one samples parameter :
centered_moment samples parameter 1 = 0.
Proof.
induction samples as [|samples IH]; [unfold centered_moment; simpl; ring|].
unfold centered_moment at 1; rewrite bernoulli_expectation_step.
transitivity (bernoulli_expectation samples parameter (fun centered => centered ^ 1)).
{ apply bernoulli_expectation_ext; intros centered; simpl; ring. }
exact IH.
Qed.
Theorem centered_moment_envelope samples parameter :
0 <= parameter <= 1 ->
forall degree, (degree <= 10)%nat ->
Rabs (centered_moment samples parameter degree) <=
moment_envelope degree (INR samples).
Proof.
intros Hparameter; induction samples as [|samples IH]; intros degree Hdegree.
{ destruct degree as [|degree]; [rewrite centered_moment_zero; simpl; rewrite Rabs_R1; lra|].
unfold centered_moment; simpl bernoulli_expectation; simpl pow.
rewrite Rmult_0_l, Rabs_R0.
destruct degree as [|[|[|[|[|[|[|[|[|[|degree]]]]]]]]]]; simpl; try lra; lia. }
assert (Hcount : 0 <= INR samples) by apply pos_INR.
rewrite S_INR.
destruct degree as [|degree].
{ rewrite centered_moment_zero; unfold moment_envelope; rewrite Rabs_R1; lra. }
destruct degree as [|degree].
{ rewrite centered_moment_one; unfold moment_envelope; rewrite Rabs_R0; lra. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 2) <= moment_envelope 2 (INR samples + 1)).
rewrite centered_moment_recurrence_2.
eapply Rle_trans with (r2 := moment_envelope 2 (INR samples) +
(1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_2; exact Hcount. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 3) <= moment_envelope 3 (INR samples + 1)).
rewrite centered_moment_recurrence_3.
eapply Rle_trans with (r2 := moment_envelope 3 (INR samples) +
(3 * moment_envelope 1 (INR samples) / 4) + (1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_3; exact Hcount. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 4) <= moment_envelope 4 (INR samples + 1)).
rewrite centered_moment_recurrence_4.
eapply Rle_trans with (r2 := moment_envelope 4 (INR samples) +
(6 * moment_envelope 2 (INR samples) / 4) + (4 * moment_envelope 1 (INR samples) / 4) + (1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_4; exact Hcount. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 5) <= moment_envelope 5 (INR samples + 1)).
rewrite centered_moment_recurrence_5.
eapply Rle_trans with (r2 := moment_envelope 5 (INR samples) +
(10 * moment_envelope 3 (INR samples) / 4) + (10 * moment_envelope 2 (INR samples) / 4) + (5 * moment_envelope 1 (INR samples) / 4) + (1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_5; exact Hcount. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 6) <= moment_envelope 6 (INR samples + 1)).
rewrite centered_moment_recurrence_6.
eapply Rle_trans with (r2 := moment_envelope 6 (INR samples) +
(15 * moment_envelope 4 (INR samples) / 4) + (20 * moment_envelope 3 (INR samples) / 4) + (15 * moment_envelope 2 (INR samples) / 4) + (6 * moment_envelope 1 (INR samples) / 4) + (1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_6; exact Hcount. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 7) <= moment_envelope 7 (INR samples + 1)).
rewrite centered_moment_recurrence_7.
eapply Rle_trans with (r2 := moment_envelope 7 (INR samples) +
(21 * moment_envelope 5 (INR samples) / 4) + (35 * moment_envelope 4 (INR samples) / 4) + (35 * moment_envelope 3 (INR samples) / 4) + (21 * moment_envelope 2 (INR samples) / 4) + (7 * moment_envelope 1 (INR samples) / 4) + (1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_7; exact Hcount. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 8) <= moment_envelope 8 (INR samples + 1)).
rewrite centered_moment_recurrence_8.
eapply Rle_trans with (r2 := moment_envelope 8 (INR samples) +
(28 * moment_envelope 6 (INR samples) / 4) + (56 * moment_envelope 5 (INR samples) / 4) + (70 * moment_envelope 4 (INR samples) / 4) + (56 * moment_envelope 3 (INR samples) / 4) + (28 * moment_envelope 2 (INR samples) / 4) + (8 * moment_envelope 1 (INR samples) / 4) + (1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_8; exact Hcount. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 9) <= moment_envelope 9 (INR samples + 1)).
rewrite centered_moment_recurrence_9.
eapply Rle_trans with (r2 := moment_envelope 9 (INR samples) +
(36 * moment_envelope 7 (INR samples) / 4) + (84 * moment_envelope 6 (INR samples) / 4) + (126 * moment_envelope 5 (INR samples) / 4) + (126 * moment_envelope 4 (INR samples) / 4) + (84 * moment_envelope 3 (INR samples) / 4) + (36 * moment_envelope 2 (INR samples) / 4) + (9 * moment_envelope 1 (INR samples) / 4) + (1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_9; exact Hcount. }
destruct degree as [|degree].
{ change (Rabs (centered_moment (S samples) parameter 10) <= moment_envelope 10 (INR samples + 1)).
rewrite centered_moment_recurrence_10.
eapply Rle_trans with (r2 := moment_envelope 10 (INR samples) +
(45 * moment_envelope 8 (INR samples) / 4) + (120 * moment_envelope 7 (INR samples) / 4) + (210 * moment_envelope 6 (INR samples) / 4) + (252 * moment_envelope 5 (INR samples) / 4) + (210 * moment_envelope 4 (INR samples) / 4) + (120 * moment_envelope 3 (INR samples) / 4) + (45 * moment_envelope 2 (INR samples) / 4) + (10 * moment_envelope 1 (INR samples) / 4) + (1 * moment_envelope 0 (INR samples) / 4)).
{ repeat apply absolute_add_bound.
- apply IH; lia.
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
- apply absolute_moment_term; [lra|apply increment_moment_bound; [exact Hparameter|lia]|apply IH; lia].
}
apply moment_envelope_step_10; exact Hcount. }
lia.
Qed.


Lemma tenth_power_nonnegative value : 0 <= value ^ 10.
Proof. pose proof (Rle_0_sqr (value ^ 5)) as Hsquare.
  unfold Rsqr in Hsquare; replace (value ^ 10) with (value ^ 5 * value ^ 5) by ring; exact Hsquare. Qed.
Lemma absolute_tenth_power value : Rabs value ^ 10 = value ^ 10.
Proof. rewrite RPow_abs; apply Rabs_right; pose proof (tenth_power_nonnegative value); lra. Qed.

Definition radius_failure {A : Type} (centered_sum : A -> R)
    (radius : R) (point : A) : bool :=
  if Rle_dec radius (Rabs (centered_sum point)) then true else false.

Theorem bernoulli_tenth_moment_tail {A : Type} (law : list (A * R))
    samples parameter (centered_sum : A -> R) radius :
  nonnegative_law law ->
  0 <= parameter <= 1 ->
  0 < radius ->
  (forall observable,
    weighted_expectation law (fun point => observable (centered_sum point)) =
    bernoulli_expectation samples parameter observable) ->
  event_probability law (radius_failure centered_sum radius) <=
    moment_envelope 10 (INR samples) / radius ^ 10.
Proof.
  intros Hlaw Hparameter Hradius Hmarginal.
  assert (Hmoment :
    weighted_expectation law (fun point => centered_sum point ^ 10) <=
    moment_envelope 10 (INR samples)).
  { rewrite (Hmarginal (fun centered => centered ^ 10)).
    change (centered_moment samples parameter 10 <= moment_envelope 10 (INR samples)).
    pose proof (centered_moment_envelope samples parameter Hparameter 10 ltac:(lia)).
    pose proof (Rle_abs (centered_moment samples parameter 10)); lra. }
  eapply Rle_trans.
  - apply (weighted_markov law (radius_failure centered_sum radius)
      (fun point => centered_sum point ^ 10) (radius ^ 10)).
    + exact Hlaw.
    + apply pow_lt; exact Hradius.
    + intros point; apply tenth_power_nonnegative.
    + intros point Hevent; unfold radius_failure in Hevent.
      destruct (Rle_dec radius (Rabs (centered_sum point))) as [Hlarge|Hsmall];
        [|discriminate].
      rewrite <- (absolute_tenth_power (centered_sum point)).
      apply pow_incr; split; lra.
  - apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; apply pow_lt; exact Hradius|exact Hmoment].
Qed.

Lemma finite_probability_sum_bound {A I : Type} (law : list (A * R))
    (indices : list I) (events : I -> A -> bool) bound :
  (forall index, In index indices -> event_probability law (events index) <= bound) ->
  real_sum (map (fun index => event_probability law (events index)) indices) <=
  INR (length indices) * bound.
Proof.
  intros Hbound; induction indices as [|index rest IH]; cbn [real_sum map length]; [change (0 <= 0 * bound); lra|].
  rewrite S_INR.
  assert (Hhead : event_probability law (events index) <= bound) by (apply Hbound; left; reflexivity).
  assert (Hrest : real_sum (map (fun index => event_probability law (events index)) rest) <= INR (length rest) * bound).
  { apply IH; intros index' Hin; apply Hbound; right; exact Hin. }
  lra.
Qed.

Definition terminal_samples : nat := Nat.pow 2 13.
Lemma sample_count_8192 : INR terminal_samples = 8192.
Proof. rewrite INR_IZR_INZ; reflexivity. Qed.
Lemma family_count_32 : INR 32 = 32.
Proof. rewrite INR_IZR_INZ; reflexivity. Qed.

Lemma terminal_family_tenth_moment_rational :
  32 * moment_envelope 10 8192 / (8192 * (21/1000)) ^ 10 < 1/20.
Proof. unfold moment_envelope; simpl; field_simplify; lra. Qed.
Lemma terminal_tenth_moment_envelope_exact :
  1024 * moment_envelope 10 8192 = 35034642400712314585088.
Proof. unfold moment_envelope; simpl; field. Qed.

(** Each marginal is an IID Bernoulli centered sum. The shared finite law
    permits arbitrary dependence across the indexed observables. *)
Theorem terminal_32_mean_family_coverage {A I : Type}
    (law : list (A * R)) (indices : list I)
    (parameter : I -> R) (centered_sum : I -> A -> R) :
  nonnegative_law law ->
  normalized_law law ->
  length indices = 32%nat ->
  (forall index, In index indices -> 0 <= parameter index <= 1) ->
  (forall index, In index indices -> forall observable,
    weighted_expectation law (fun point => observable (centered_sum index point)) =
    bernoulli_expectation terminal_samples (parameter index) observable) ->
  event_probability law (fun point =>
    existsb (fun index => radius_failure (centered_sum index) (8192 * (21/1000)) point) indices) <= 1/20.
Proof.
  intros Hlaw Hnormalized Hlength Hparameter Hmarginal.
  eapply Rle_trans; [apply finite_union_bound; exact Hlaw|].
  eapply Rle_trans with (r2 := INR (length indices) *
    (moment_envelope 10 (INR terminal_samples) / (8192 * (21/1000)) ^ 10)).
  - apply finite_probability_sum_bound; intros index Hin.
    apply (bernoulli_tenth_moment_tail law terminal_samples (parameter index) (centered_sum index) (8192 * (21/1000))); [exact Hlaw|apply Hparameter; exact Hin|lra|].
    apply Hmarginal; exact Hin.
  - rewrite Hlength, family_count_32, sample_count_8192.
    pose proof terminal_family_tenth_moment_rational; lra.
Qed.

Print Assumptions centered_moment_envelope.
Print Assumptions bernoulli_tenth_moment_tail.
Print Assumptions terminal_tenth_moment_envelope_exact.
Print Assumptions terminal_family_tenth_moment_rational.
Print Assumptions terminal_32_mean_family_coverage.


(** The convolution operator is the expectation of an explicit finite law. *)
Definition weighted_push (law : list (R * R)) (transform : R -> R)
    (mass : R) : list (R * R) :=
  map (fun point => (transform (fst point), mass * snd point)) law.
Fixpoint bernoulli_law (samples : nat) (parameter : R) : list (R * R) :=
  match samples with
  | O => [(0,1)]
  | S previous =>
      weighted_push (bernoulli_law previous parameter) (fun centered => centered-parameter) (1-parameter) ++
      weighted_push (bernoulli_law previous parameter) (fun centered => centered+(1-parameter)) parameter
  end.
Lemma weighted_expectation_append {A : Type} (left right : list (A * R)) observable :
  weighted_expectation (left ++ right) observable =
  weighted_expectation left observable + weighted_expectation right observable.
Proof. induction left as [|[point weight] rest IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma weighted_push_expectation law transform mass observable :
  weighted_expectation (weighted_push law transform mass) observable =
  mass * weighted_expectation law (fun centered => observable (transform centered)).
Proof. induction law as [|[point weight] rest IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma bernoulli_law_expectation samples parameter observable :
  weighted_expectation (bernoulli_law samples parameter) observable =
  bernoulli_expectation samples parameter observable.
Proof. revert observable; induction samples; intros observable; simpl; [ring|].
  rewrite weighted_expectation_append, !weighted_push_expectation, !IHsamples; reflexivity. Qed.
Lemma weighted_push_nonnegative law transform mass :
  nonnegative_law law -> 0 <= mass -> nonnegative_law (weighted_push law transform mass).
Proof. intros Hlaw Hmass; induction Hlaw as [|[point weight] rest Hweight Hrest IH]; simpl.
  - constructor.
  - constructor; [simpl in *; nra|exact IH].
Qed.
Lemma bernoulli_law_nonnegative samples parameter :
  0 <= parameter <= 1 -> nonnegative_law (bernoulli_law samples parameter).
Proof. intros Hparameter; induction samples; simpl.
  - repeat constructor; simpl; lra.
  - apply Forall_app; split; apply weighted_push_nonnegative; try exact IHsamples; lra.
Qed.
Lemma bernoulli_law_normalized samples parameter :
  normalized_law (bernoulli_law samples parameter).
Proof. unfold normalized_law; rewrite bernoulli_law_expectation; apply bernoulli_expectation_one. Qed.
Print Assumptions bernoulli_law_expectation.
Print Assumptions bernoulli_law_nonnegative.
Print Assumptions bernoulli_law_normalized.

