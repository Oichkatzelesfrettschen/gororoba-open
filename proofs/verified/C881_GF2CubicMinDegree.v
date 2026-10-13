(** * GF(2) minimum separating degree for a fixed PG(3,2) partition.

    The definitions [pg32_labels] and [pg32_classes] fix 15 point labels
    and their Boolean classification. The kernel checks all 2048 coefficient
    choices over the 11 four-variable multilinear monomials of degree <= 2,
    including the constant monomial. Every choice fails to match the fixed
    classification. The explicit cubic witness matches it and has degree 3.

    The coefficient-vector theorem establishes the lower bound for every
    four-variable multilinear polynomial of degree <= 2. The statements
    concern only the concrete lists in this file. They do not parse or verify
    a runtime dataset, identify every possible PG(3,2) partition, or establish
    a physical interpretation.

    Source convention: algebra_analysis::projective_geometry test
    test_determine_exact_degree_dim32 uses the XOR signature labels below.
    The Boolean polarity here is true for the eight heptacross components
    and false for the seven mixed-degree components. *)

From OpenGororoba Require Import GF2Algebra.
From Stdlib Require Import Bool Arith Lia List.
Import ListNotations.

(** The 15 PG(3,2) point labels, in component discovery order.
    Each label is a 4-bit XOR signature of the cross-assessor component. *)
Definition pg32_labels : list nat :=
  [3; 2; 5; 4; 7; 6; 9; 8; 11; 10; 13; 12; 15; 14; 1].

(** Classification for the cubic witness polynomial.
    true = heptacross (84 edges, poly evals to 1),
    false = mixed-degree (poly evals to 0).
    Polarity matches the cubic witness output. *)
Definition pg32_classes : list bool :=
  [true; true; true; true; true; true; false; true;
   false; false; false; false; false; false; true].

(** Sanity check: 15 labels and 15 classes. *)
Theorem pg32_length_labels : length pg32_labels = 15.
Proof. reflexivity. Qed.

Theorem pg32_length_classes : length pg32_classes = 15.
Proof. reflexivity. Qed.

(** --- Degree-1 (linear) monomials fail to separate --- *)

(** All degree-1 monomials over 4 bits: single-bit masks 1, 2, 4, 8. *)
Definition degree1_monomials : list nat := [1; 2; 4; 8].

(** No single degree-1 monomial separates. *)
Theorem degree1_mono1_fails : separates_b pg32_labels pg32_classes [1] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_mono2_fails : separates_b pg32_labels pg32_classes [2] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_mono4_fails : separates_b pg32_labels pg32_classes [4] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_mono8_fails : separates_b pg32_labels pg32_classes [8] = false.
Proof. vm_compute. reflexivity. Qed.

(** Some representative degree-1 combinations also fail. *)
Theorem degree1_combo_12_fails : separates_b pg32_labels pg32_classes [1; 2] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_14_fails : separates_b pg32_labels pg32_classes [1; 4] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_18_fails : separates_b pg32_labels pg32_classes [1; 8] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_24_fails : separates_b pg32_labels pg32_classes [2; 4] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_28_fails : separates_b pg32_labels pg32_classes [2; 8] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_48_fails : separates_b pg32_labels pg32_classes [4; 8] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_124_fails : separates_b pg32_labels pg32_classes [1; 2; 4] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_128_fails : separates_b pg32_labels pg32_classes [1; 2; 8] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_148_fails : separates_b pg32_labels pg32_classes [1; 4; 8] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_248_fails : separates_b pg32_labels pg32_classes [2; 4; 8] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree1_combo_1248_fails : separates_b pg32_labels pg32_classes [1; 2; 4; 8] = false.
Proof. vm_compute. reflexivity. Qed.

(** --- Degree-2 (quadratic) monomials: adding them still fails --- *)

(** Degree-2 monomials: all 2-bit masks. *)
(** 3=0b0011, 5=0b0101, 6=0b0110, 9=0b1001, 10=0b1010, 12=0b1100 *)

(** A representative set of degree <= 2 combinations that fail. *)
Theorem degree2_mono3_fails : separates_b pg32_labels pg32_classes [3] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree2_mono5_fails : separates_b pg32_labels pg32_classes [5] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree2_mono6_fails : separates_b pg32_labels pg32_classes [6] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree2_mono9_fails : separates_b pg32_labels pg32_classes [9] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree2_mono10_fails : separates_b pg32_labels pg32_classes [10] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem degree2_mono12_fails : separates_b pg32_labels pg32_classes [12] = false.
Proof. vm_compute. reflexivity. Qed.

(** The constant mask 0 and every one-bit or two-bit mask below 16 form
    the complete four-variable multilinear basis through degree 2. *)
Definition degree2_monomials : list nat :=
  [0; 1; 2; 3; 4; 5; 6; 8; 9; 10; 12].

Theorem degree2_monomials_filtered :
  degree2_monomials =
    filter (fun monomial => Nat.leb (monomial_degree monomial 4) 2)
      (seq 0 16).
Proof. vm_compute. reflexivity. Qed.

Theorem degree2_monomials_characterization :
  forall monomial,
    In monomial degree2_monomials <->
      monomial < 16 /\ monomial_degree monomial 4 <= 2.
Proof.
  intros monomial.
  rewrite degree2_monomials_filtered, filter_In, in_seq, Nat.leb_le.
  lia.
Qed.

(** Each branch omits or includes one basis monomial, encoding its GF(2)
    coefficient as false or true. The empty subset encodes the zero polynomial. *)
Fixpoint monomial_subsets (monomials : list nat) : list (list nat) :=
  match monomials with
  | [] => [[]]
  | monomial :: rest =>
      let subsets := monomial_subsets rest in
      subsets ++ map (fun subset => monomial :: subset) subsets
  end.

Definition degree2_candidates : list (list nat) :=
  monomial_subsets degree2_monomials.

Theorem degree2_candidate_count : length degree2_candidates = 2048.
Proof. vm_compute. reflexivity. Qed.

(** Coefficients follow the order of [degree2_monomials]. The length premise
    in [degree2_coefficients_fail] supplies exactly one coefficient per mask. *)
Fixpoint coefficient_support (monomials : list nat) (coefficients : list bool)
    : list nat :=
  match monomials, coefficients with
  | monomial :: rest, coefficient :: remaining =>
      if coefficient then monomial :: coefficient_support rest remaining
      else coefficient_support rest remaining
  | _, _ => []
  end.

Theorem coefficient_support_enumerated :
  forall monomials coefficients,
    length coefficients = length monomials ->
    In (coefficient_support monomials coefficients) (monomial_subsets monomials).
Proof.
  induction monomials as [| monomial rest induction_hypothesis];
    intros coefficients matching_length.
  - destruct coefficients as [| coefficient remaining].
    + simpl. auto.
    + discriminate matching_length.
  - destruct coefficients as [| coefficient remaining].
    + discriminate matching_length.
    + simpl in matching_length.
      inversion matching_length as [remaining_length].
      specialize (induction_hypothesis remaining remaining_length).
      destruct coefficient; simpl; apply in_or_app.
      * right. apply in_map. exact induction_hypothesis.
      * left. exact induction_hypothesis.
Qed.

(** Kernel reduction evaluates the complete finite coefficient search. *)
Theorem degree2_all_candidates_fail :
  forallb
    (fun candidate => negb (separates_b pg32_labels pg32_classes candidate))
    degree2_candidates = true.
Proof. vm_compute. reflexivity. Qed.

Theorem degree2_candidate_fails :
  forall candidate,
    In candidate degree2_candidates ->
    separates_b pg32_labels pg32_classes candidate = false.
Proof.
  intros candidate candidate_membership.
  pose proof degree2_all_candidates_fail as all_candidates_fail.
  rewrite forallb_forall in all_candidates_fail.
  specialize (all_candidates_fail candidate candidate_membership).
  now apply negb_true_iff in all_candidates_fail.
Qed.

Theorem degree2_coefficients_fail :
  forall coefficients,
    length coefficients = 11 ->
    separates_b pg32_labels pg32_classes
      (coefficient_support degree2_monomials coefficients) = false.
Proof.
  intros coefficients coefficient_count.
  apply degree2_candidate_fails.
  unfold degree2_candidates.
  apply coefficient_support_enumerated.
  exact coefficient_count.
Qed.

(** --- Cubic witness: degree-3 polynomial SUCCEEDS --- *)

(** The cubic witness polynomial: monomials [1;2;3;4;5;6;7;8].
    This includes:
    - degree-1: 1 (x0), 2 (x1), 4 (x2), 8 (x3)
    - degree-2: 3 (x0*x1), 5 (x0*x2), 6 (x1*x2)
    - degree-3: 7 (x0*x1*x2)
    Maximum monomial degree is 3 (the mask 7 = 0b0111). *)
Definition cubic_witness : list nat := [1; 2; 3; 4; 5; 6; 7; 8].

(*<*cubicwit>*)
(** The cubic witness separates the PG(3,2) partition. *)
Theorem cubic_witness_separates :
  separates_b pg32_labels pg32_classes cubic_witness = true.
Proof. vm_compute. reflexivity. Qed.
(*</cubicwit>*)

(** The witness has maximum degree 3 (mask 7 = 0b0111 has 3 bits set). *)
Theorem cubic_witness_max_degree :
  max_degree cubic_witness 4 = 3.
Proof. vm_compute. reflexivity. Qed.

(** The fixed partition has a cubic witness and rejects every degree <= 2
    coefficient vector in the complete four-variable multilinear basis. *)
Theorem fixed_partition_minimum_separating_degree :
  (forall coefficients,
    length coefficients = 11 ->
    separates_b pg32_labels pg32_classes
      (coefficient_support degree2_monomials coefficients) = false) /\
  separates_b pg32_labels pg32_classes cubic_witness = true /\
  max_degree cubic_witness 4 = 3.
Proof.
  split.
  - exact degree2_coefficients_fail.
  - split.
    + exact cubic_witness_separates.
    + exact cubic_witness_max_degree.
Qed.
