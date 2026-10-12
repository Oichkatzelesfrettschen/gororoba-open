(** Scalar averaging loses multiplication information; average/detail
    coordinates preserve the exact canonical-rational pair. The pair
    multiplication law is the scalar Cayley-Dickson doubling instance. *)

From Stdlib Require Import QArith.Qcanon Field.

Open Scope Qc_scope.

(* Canonical rational coordinates make equality literal equality. *)
Definition scalar_pair := (Qc * Qc)%type.
Definition pair_zero : scalar_pair := (0, 0).

(* Scalar Cayley-Dickson doubling has the complex multiplication law. *)
Definition pair_product (left right : scalar_pair) : scalar_pair :=
  (fst left * fst right - snd right * snd left,
   snd right * fst left + snd left * fst right).

Definition pair_average (value : scalar_pair) : Qc :=
  (fst value + snd value) / (1 + 1).

Definition pair_detail (value : scalar_pair) : Qc :=
  (fst value - snd value) / (1 + 1).

Definition average_detail (value : scalar_pair) : scalar_pair :=
  (pair_average value, pair_detail value).

Definition reconstruct (coordinates : scalar_pair) : scalar_pair :=
  (fst coordinates + snd coordinates, fst coordinates - snd coordinates).

Definition kernel_witness : scalar_pair := (1, Qcopp 1).
Definition right_multiplier : scalar_pair := (0, 1).

Lemma kernel_witness_average : pair_average kernel_witness = 0.
Proof. unfold pair_average, kernel_witness; cbn; field; discriminate. Qed.

Lemma zero_average : pair_average pair_zero = 0.
Proof. unfold pair_average, pair_zero; cbn; field; discriminate. Qed.

Lemma witness_product_average :
  pair_average (pair_product kernel_witness right_multiplier) = 1.
Proof.
  unfold pair_average, pair_product, kernel_witness, right_multiplier;
    cbn; field; discriminate.
Qed.

Lemma zero_product_average :
  pair_average (pair_product pair_zero right_multiplier) = 0.
Proof.
  unfold pair_average, pair_product, pair_zero, right_multiplier;
    cbn; field; discriminate.
Qed.

(* Multiplication cannot descend to average coordinates alone: equal
   averages can acquire different averages after the same multiplication. *)
Theorem average_product_does_not_descend :
  ~ exists average_product : Qc -> Qc -> Qc,
      forall left right : scalar_pair,
        pair_average (pair_product left right) =
        average_product (pair_average left) (pair_average right).
Proof.
  intros [average_product preserves_product].
  pose proof (preserves_product kernel_witness right_multiplier)
    as witness_identity.
  pose proof (preserves_product pair_zero right_multiplier)
    as zero_identity.
  rewrite witness_product_average, kernel_witness_average in witness_identity.
  rewrite zero_product_average, zero_average in zero_identity.
  apply Q_apart_0_1.
  transitivity (average_product 0 (pair_average right_multiplier)).
  - exact witness_identity.
  - symmetry; exact zero_identity.
Qed.

Theorem reconstruction_after_average_detail :
  forall value, reconstruct (average_detail value) = value.
Proof.
  intros [first_coordinate second_coordinate].
  unfold reconstruct, average_detail, pair_average, pair_detail; cbn.
  f_equal; field; discriminate.
Qed.

Theorem average_detail_after_reconstruction :
  forall coordinates, average_detail (reconstruct coordinates) = coordinates.
Proof.
  intros [average_coordinate detail_coordinate].
  unfold reconstruct, average_detail, pair_average, pair_detail; cbn.
  f_equal; field; discriminate.
Qed.

Theorem average_detail_injective :
  forall left right, average_detail left = average_detail right -> left = right.
Proof.
  intros left right same_coordinates.
  rewrite <- (reconstruction_after_average_detail left).
  rewrite <- (reconstruction_after_average_detail right).
  now rewrite same_coordinates.
Qed.

Print Assumptions kernel_witness_average.
Print Assumptions zero_average.
Print Assumptions witness_product_average.
Print Assumptions zero_product_average.
Print Assumptions average_product_does_not_descend.
Print Assumptions reconstruction_after_average_detail.
Print Assumptions average_detail_after_reconstruction.
Print Assumptions average_detail_injective.
