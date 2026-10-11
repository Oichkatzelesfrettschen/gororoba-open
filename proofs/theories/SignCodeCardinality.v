(** Exact finite cardinality of the normalized Cayley-Dickson sign code.

    Boolean tables give concrete finite representatives of functions on the
    cube. The enumeration contains each admitted codeword exactly once;
    its length is therefore a cardinality statement, not a dimension label. *)

From Stdlib Require Import Bool Arith Lia List.
From OpenGororoba Require Import SchreierSignCode.
Import ListNotations.

Fixpoint boolean_table (order : nat) : Type :=
  match order with O => bool | S lower => (boolean_table lower * boolean_table lower)%type end.

Fixpoint table_lookup (order : nat) : boolean_table order -> cube order -> bool :=
  match order with
  | O => fun table _ => table
  | S lower => fun table input =>
      table_lookup lower (if snd input then snd table else fst table) (fst input)
  end.

Fixpoint tabulate (order : nat) : (cube order -> bool) -> boolean_table order :=
  match order with
  | O => fun function => function tt
  | S lower => fun function =>
      (tabulate lower (fun input => function (input, false)),
       tabulate lower (fun input => function (input, true)))
  end.

Lemma table_lookup_tabulate : forall order function input,
    table_lookup order (tabulate order function) input = function input.
Proof.
  induction order; intros function input.
  - destruct input. reflexivity.
  - destruct input as [input high]. destruct high; simpl; apply IHorder.
Qed.

Lemma table_extensional : forall order (first second : boolean_table order),
    (forall input, table_lookup order first input = table_lookup order second input) -> first = second.
Proof.
  induction order; intros first second equal.
  - exact (equal tt).
  - destruct first as [first_low first_high], second as [second_low second_high].
    f_equal; apply IHorder.
    + intros input. exact (equal (input, false)).
    + intros input. exact (equal (input, true)).
Qed.

Fixpoint supported_tables (order : nat) : (cube order -> bool) -> list (boolean_table order) :=
  match order with
  | O => fun allowed => if allowed tt then [false; true] else [false]
  | S lower => fun allowed => list_prod
      (supported_tables lower (fun mask => allowed (mask, false)))
      (supported_tables lower (fun mask => allowed (mask, true)))
  end.

Lemma supported_tables_spec : forall order allowed table,
    In table (supported_tables order allowed) <->
    forall mask, allowed mask = false -> table_lookup order table mask = false.
Proof.
  induction order; intros allowed table.
  - cbn [supported_tables table_lookup].
    destruct (allowed tt) eqn:admission; simpl; split; intros hypothesis.
    + intros [] excluded. congruence.
    + destruct table; auto.
    + destruct hypothesis as [equal | impossible]; [subst table | contradiction].
      intros [] excluded. reflexivity.
    + left. symmetry. exact (hypothesis tt admission).
  - destruct table as [low high]. cbn [supported_tables]. split.
    + intros member. apply in_prod_iff in member. destruct member as [low_allowed high_allowed].
      pose proof (proj1 (IHorder (fun mask => allowed (mask, false)) low) low_allowed) as low_admitted.
      pose proof (proj1 (IHorder (fun mask => allowed (mask, true)) high) high_allowed) as high_admitted.
      intros [mask high_bit]. destruct high_bit; simpl; auto.
    + intros admitted. apply in_prod_iff. split.
      * apply (proj2 (IHorder (fun mask => allowed (mask, false)) low)).
        intros mask excluded. exact (admitted (mask, false) excluded).
      * apply (proj2 (IHorder (fun mask => allowed (mask, true)) high)).
        intros mask excluded. exact (admitted (mask, true) excluded).
Qed.

Lemma nodup_injective_map : forall (Input Output : Type) (function : Input -> Output) values,
    (forall first second, function first = function second -> first = second) ->
    NoDup values -> NoDup (map function values).
Proof.
  intros Input Output function values injective unique. induction unique; simpl.
  - constructor.
  - constructor; [| exact IHunique]. intros member. apply in_map_iff in member.
    destruct member as [other [equal member]]. apply injective in equal. subst other. contradiction.
Qed.

Lemma nodup_cartesian_product : forall (Left Right : Type) (left : list Left) (right : list Right),
    NoDup left -> NoDup right -> NoDup (list_prod left right).
Proof.
  intros Left Right left right left_unique right_unique. induction left_unique; simpl.
  - constructor.
  - apply NoDup_app.
    + apply nodup_injective_map; [intros first second equal; inversion equal; reflexivity | exact right_unique].
    + exact IHleft_unique.
    + intros [first second] member conflict. apply in_map_iff in member.
      destruct member as [value [equal member]]. inversion equal; subst.
      apply in_prod_iff in conflict. destruct conflict. contradiction.
Qed.

Lemma supported_tables_unique : forall order allowed, NoDup (supported_tables order allowed).
Proof.
  induction order; intros allowed.
  - simpl. destruct (allowed tt); repeat constructor; simpl; intuition discriminate.
  - simpl. apply nodup_cartesian_product; apply IHorder.
Qed.

Lemma supported_tables_length : forall order allowed,
    length (supported_tables order allowed) = 2 ^ (cube_count order allowed).
Proof.
  induction order; intros allowed.
  - simpl. destruct (allowed tt); reflexivity.
  - simpl. rewrite length_prod, !IHorder, Nat.pow_add_r. reflexivity.
Qed.

Definition anf_table (order : nat) (coefficients : boolean_table order) : boolean_table order :=
  tabulate order (anf_evaluate order (table_lookup order coefficients)).

Lemma anf_table_injective : forall order first second,
    anf_table order first = anf_table order second -> first = second.
Proof.
  intros order first second equal. apply table_extensional.
  apply anf_evaluate_injective. intros input.
  pose proof (f_equal (fun table => table_lookup order table input) equal) as values.
  unfold anf_table in values. rewrite !table_lookup_tabulate in values. exact values.
Qed.

Definition normalized_code_tables (order : nat) : list (boolean_table (S (S (S order)))) :=
  map (anf_table (S (S (S order))))
    (supported_tables (S (S (S order))) (normalized_basis_mask (S (S order)))).

Theorem normalized_code_tables_spec : forall order table,
    In table (normalized_code_tables order) <->
    normalized_sign_span (S (S (S order))) (table_lookup (S (S (S order))) table).
Proof.
  intros order table. unfold normalized_code_tables. rewrite in_map_iff. split.
  - intros [coefficients [equal admitted]]. subst table. apply normalized_anf_spanning.
    exists (table_lookup (S (S (S order))) coefficients). split.
    + exact (proj1 (supported_tables_spec (S (S (S order)))
        (normalized_basis_mask (S (S order))) coefficients) admitted).
    + intros input. unfold anf_table. apply table_lookup_tabulate.
  - intros admitted. apply normalized_anf_spanning in admitted.
    destruct admitted as [coefficients [supported value]].
    exists (tabulate (S (S (S order))) coefficients). split.
    + apply table_extensional. intros input. unfold anf_table. rewrite table_lookup_tabulate, value.
      apply anf_evaluate_extensional. intros mask. apply table_lookup_tabulate.
    + apply (proj2 (supported_tables_spec (S (S (S order)))
        (normalized_basis_mask (S (S order))) (tabulate (S (S (S order))) coefficients))).
      intros mask excluded. rewrite table_lookup_tabulate. apply supported. exact excluded.
Qed.

Theorem normalized_code_tables_unique : forall order, NoDup (normalized_code_tables order).
Proof.
  intros order. unfold normalized_code_tables. apply nodup_injective_map.
  - apply anf_table_injective.
  - apply supported_tables_unique.
Qed.

Theorem normalized_code_cardinality : forall order,
    length (normalized_code_tables order) = 2 ^ (2 ^ (S (S order)) - 1).
Proof.
  intros order. unfold normalized_code_tables.
  rewrite length_map, supported_tables_length, normalized_anf_basis_cardinality. reflexivity.
Qed.

Print Assumptions table_lookup_tabulate.
Print Assumptions table_extensional.
Print Assumptions supported_tables_spec.
Print Assumptions nodup_injective_map.
Print Assumptions nodup_cartesian_product.
Print Assumptions supported_tables_unique.
Print Assumptions supported_tables_length.
Print Assumptions anf_table_injective.
Print Assumptions normalized_code_tables_spec.
Print Assumptions normalized_code_tables_unique.
Print Assumptions normalized_code_cardinality.
