(** Reversible Boolean predicates and signed-XOR basis actions.

    A target flip is reversible when its predicate ignores the toggled bit.
    Ordered words compose those flips. Controlled basis-pair semantics retain
    both the label and the Boolean sign, including relative control phases.
    The signed-XOR obstruction concerns label motion; diagonal signs survive
    when the label action fixes the origin. The N=21 examples use the complete
    five-bit register with identity padding on invalid residues. *)

From Stdlib Require Import PeanoNat Bool List.
Import ListNotations.

Section TargetFlip.
  Context {State : Type}.
  Variable toggle : State -> State.
  Variable predicate : State -> bool.
  Hypothesis toggle_twice : forall state, toggle (toggle state) = state.
  Hypothesis target_excluded : forall state, predicate (toggle state) = predicate state.

  Definition target_flip (state : State) : State :=
    if predicate state then toggle state else state.

  Theorem target_flip_involutive : forall state,
    target_flip (target_flip state) = state.
  Proof.
    intros state. unfold target_flip.
    destruct (predicate state) eqn:selected; [| rewrite selected; reflexivity].
    rewrite target_excluded, selected. apply toggle_twice.
  Qed.

  Theorem target_flip_injective : forall left right,
    target_flip left = target_flip right -> left = right.
  Proof.
    intros left right same_output.
    apply (f_equal target_flip) in same_output.
    now rewrite !target_flip_involutive in same_output.
  Qed.

  Theorem target_flip_surjective : forall output,
    exists input, target_flip input = output.
  Proof. intros output. exists (target_flip output). apply target_flip_involutive. Qed.
End TargetFlip.

(** Mask disjointness makes the cube predicate invariant under the target
    toggle. The proof applies to every natural label and every toggle mask. *)
Theorem masked_toggle_invariant : forall label mask toggle_mask,
  Nat.land mask toggle_mask = 0 ->
  Nat.land (Nat.lxor label toggle_mask) mask = Nat.land label mask.
Proof.
  intros label mask toggle_mask disjoint. apply Nat.bits_inj. intros bit.
  pose proof (f_equal (fun value => Nat.testbit value bit) disjoint) as excluded_bit.
  cbn beta in excluded_bit.
  rewrite Nat.land_spec, Nat.bits_0 in excluded_bit.
  rewrite !Nat.land_spec, Nat.lxor_spec.
  destruct (Nat.testbit mask bit), (Nat.testbit toggle_mask bit), (Nat.testbit label bit);
    simpl in *; congruence.
Qed.

Definition cube_flip (target mask selected label : nat) : nat :=
  target_flip (fun value => Nat.lxor value (2 ^ target))
    (fun value => Nat.eqb (Nat.land value mask) selected) label.

Theorem cube_flip_involutive : forall target mask selected,
  Nat.land mask (2 ^ target) = 0 ->
  forall label, cube_flip target mask selected (cube_flip target mask selected label) = label.
Proof.
  intros target mask selected excluded. unfold cube_flip. apply target_flip_involutive.
  - intros label. rewrite Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_r. reflexivity.
  - intros label. rewrite masked_toggle_invariant; [reflexivity | exact excluded].
Qed.

Theorem cube_flip_bijective : forall target mask selected,
  Nat.land mask (2 ^ target) = 0 ->
  (forall left right,
    cube_flip target mask selected left = cube_flip target mask selected right -> left = right) /\
  (forall output, exists input, cube_flip target mask selected input = output).
Proof.
  intros target mask selected excluded. split.
  - intros left right same_output.
    apply (f_equal (cube_flip target mask selected)) in same_output.
    now rewrite !cube_flip_involutive in same_output.
  - intros output. exists (cube_flip target mask selected output).
    apply cube_flip_involutive. exact excluded.
Qed.

Theorem target_dependent_predicate_breaks_involution :
  cube_flip 0 1 0 (cube_flip 0 1 0 0) <> 0.
Proof. vm_compute. discriminate. Qed.

Fixpoint run_word {State : Type} (word : list (State -> State)) (state : State) : State :=
  match word with
  | [] => state
  | gate :: rest => run_word rest (gate state)
  end.

Theorem run_word_append : forall State (first second : list (State -> State)) state,
  run_word (first ++ second) state = run_word second (run_word first state).
Proof.
  intros State first. induction first; intros second state; simpl; auto.
Qed.

Theorem reverse_word_inverse : forall State (word : list (State -> State)),
  Forall (fun gate => forall state, gate (gate state) = state) word ->
  forall state, run_word (rev word) (run_word word state) = state.
Proof.
  intros State word reversible. induction reversible; intros state; simpl; [reflexivity |].
  rewrite run_word_append, IHreversible. simpl. apply H.
Qed.

Theorem word_reverse_inverse : forall State (word : list (State -> State)),
  Forall (fun gate => forall state, gate (gate state) = state) word ->
  forall state, run_word word (run_word (rev word) state) = state.
Proof.
  intros State word reversible state.
  pose proof (Forall_rev reversible) as reversed_reversible.
  pose proof (reverse_word_inverse State (rev word) reversed_reversible state) as inverse.
  now rewrite rev_involutive in inverse.
Qed.

Definition controlled {State : Type} (action : State -> State) (control : bool) (state : State) :=
  if control then action state else state.

Theorem disabled_control_identity : forall State (action : State -> State) state,
  controlled action false state = state.
Proof. reflexivity. Qed.

Theorem enabled_control_action : forall State (action : State -> State) state,
  controlled action true state = action state.
Proof. reflexivity. Qed.

Theorem controlled_composition : forall State (first second : State -> State) control state,
  controlled second control (controlled first control state) =
  controlled (fun value => second (first value)) control state.
Proof. intros State first second [] state; reflexivity. Qed.

Record signed_xor_action := SignedXor {
  action_offset : nat;
  action_phase : nat -> bool
}.

Definition signed_apply (action : signed_xor_action) (phase : bool) (label : nat) : bool * nat :=
  (xorb phase (action_phase action label), Nat.lxor label (action_offset action)).

(** The first action executes before the second action. The second phase
    reads the translated label rather than the original label. *)
Definition signed_compose (first second : signed_xor_action) : signed_xor_action :=
  SignedXor (Nat.lxor (action_offset first) (action_offset second))
    (fun label => xorb (action_phase first label)
      (action_phase second (Nat.lxor label (action_offset first)))).

Theorem signed_composition_exact : forall first second phase label,
  let intermediate := signed_apply first phase label in
  signed_apply second (fst intermediate) (snd intermediate) =
  signed_apply (signed_compose first second) phase label.
Proof.
  intros first second phase label. unfold signed_apply, signed_compose. simpl.
  rewrite Nat.lxor_assoc, xorb_assoc. reflexivity.
Qed.

Definition controlled_signed (action : signed_xor_action) (control phase : bool) (label : nat) :=
  if control then signed_apply action phase label else (phase, label).

Theorem controlled_signed_label : forall action control phase label,
  snd (controlled_signed action control phase label) =
  if control then Nat.lxor label (action_offset action) else label.
Proof. intros action [] phase label; reflexivity. Qed.

Theorem controlled_signed_phase : forall action control phase label,
  fst (controlled_signed action control phase label) =
  xorb phase (andb control (action_phase action label)).
Proof. intros action [] [] label; reflexivity. Qed.

Theorem controlled_signed_disabled_identity : forall action phase label,
  controlled_signed action false phase label = (phase, label).
Proof. reflexivity. Qed.

Theorem controlled_signed_composition : forall first second control phase label,
  let intermediate := controlled_signed first control phase label in
  controlled_signed second control (fst intermediate) (snd intermediate) =
  controlled_signed (signed_compose first second) control phase label.
Proof.
  intros first second [] phase label; [apply signed_composition_exact | reflexivity].
Qed.

Fixpoint run_signed_word (word : list signed_xor_action) (phase : bool) (label : nat) : bool * nat :=
  match word with
  | [] => (phase, label)
  | action :: rest =>
      let intermediate := signed_apply action phase label in
      run_signed_word rest (fst intermediate) (snd intermediate)
  end.

Fixpoint word_offset (word : list signed_xor_action) : nat :=
  match word with
  | [] => 0
  | action :: rest => Nat.lxor (action_offset action) (word_offset rest)
  end.

Theorem signed_word_label_projection : forall word phase label,
  snd (run_signed_word word phase label) = Nat.lxor label (word_offset word).
Proof.
  induction word; intros phase label; simpl.
  - now rewrite Nat.lxor_0_r.
  - rewrite IHword. simpl. now rewrite Nat.lxor_assoc.
Qed.

Theorem signed_xor_fixed_zero_label_identity : forall action,
  snd (signed_apply action false 0) = 0 ->
  forall phase label, snd (signed_apply action phase label) = label.
Proof.
  intros action fixes_zero phase label.
  unfold signed_apply in *. simpl in *.
  rewrite Nat.lxor_0_l in fixes_zero. rewrite fixes_zero, Nat.lxor_0_r. reflexivity.
Qed.

Theorem signed_word_fixed_zero_label_identity : forall word,
  snd (run_signed_word word false 0) = 0 ->
  forall phase label, snd (run_signed_word word phase label) = label.
Proof.
  intros word fixes_zero phase label.
  rewrite signed_word_label_projection, Nat.lxor_0_l in fixes_zero.
  rewrite signed_word_label_projection, fixes_zero, Nat.lxor_0_r. reflexivity.
Qed.

Definition nonconstant_diagonal := SignedXor 0 (fun label => Nat.testbit label 0).

Theorem diagonal_phase_preserves_labels : forall phase label,
  snd (signed_apply nonconstant_diagonal phase label) = label.
Proof. intros phase label. unfold signed_apply, nonconstant_diagonal. simpl. apply Nat.lxor_0_r. Qed.

Theorem diagonal_phase_is_nontrivial :
  signed_apply nonconstant_diagonal false 0 = (false, 0) /\
  signed_apply nonconstant_diagonal false 1 = (true, 1).
Proof. vm_compute. split; reflexivity. Qed.

Theorem diagonal_control_relative_phase :
  controlled_signed nonconstant_diagonal false false 1 <>
  controlled_signed nonconstant_diagonal true false 1.
Proof. vm_compute. discriminate. Qed.

Definition n21_multiplier (multiplier label : nat) : nat :=
  if label <? 21 then (multiplier * label) mod 21 else label.

Definition affine_on_five_bits (mapping : nat -> nat) : Prop :=
  forall left right, left < 32 -> right < 32 ->
  mapping (Nat.lxor left right) =
  Nat.lxor (Nat.lxor (mapping left) (mapping right)) (mapping 0).

Theorem n21_fixes_origin : forall multiplier, n21_multiplier multiplier 0 = 0.
Proof. intros multiplier. unfold n21_multiplier. rewrite Nat.mul_0_r. reflexivity. Qed.

Theorem n21_moves_one : forall multiplier, In multiplier [2; 4; 16] ->
  n21_multiplier multiplier 1 <> 1.
Proof.
  intros multiplier member. simpl in member.
  destruct member as [<- | [<- | [<- | []]]]; vm_compute; discriminate.
Qed.

Theorem n21_nonaffine : forall multiplier, In multiplier [2; 4; 16] ->
  ~ affine_on_five_bits (n21_multiplier multiplier).
Proof.
  intros multiplier member affine.
  assert (left_bound : 8 < 32) by (repeat constructor).
  assert (right_bound : 16 < 32) by (repeat constructor).
  specialize (affine 8 16 left_bound right_bound).
  simpl in member. destruct member as [<- | [<- | [<- | []]]];
    vm_compute in affine; discriminate.
Qed.

Theorem n21_excludes_signed_xor_words : forall multiplier,
  In multiplier [2; 4; 16] -> forall word,
  ~ (forall label, label < 32 ->
    snd (run_signed_word word false label) = n21_multiplier multiplier label).
Proof.
  intros multiplier member word implements.
  assert (origin_bound : 0 < 32) by (repeat constructor).
  assert (one_bound : 1 < 32) by (repeat constructor).
  pose proof (implements 0 origin_bound) as fixes_zero.
  rewrite n21_fixes_origin in fixes_zero.
  pose proof (implements 1 one_bound) as moves_one.
  rewrite (signed_word_fixed_zero_label_identity word fixes_zero false 1) in moves_one.
  apply (n21_moves_one multiplier member). symmetry. exact moves_one.
Qed.

Print Assumptions target_flip_involutive.
Print Assumptions target_flip_injective.
Print Assumptions target_flip_surjective.
Print Assumptions masked_toggle_invariant.
Print Assumptions cube_flip_involutive.
Print Assumptions cube_flip_bijective.
Print Assumptions target_dependent_predicate_breaks_involution.
Print Assumptions run_word_append.
Print Assumptions reverse_word_inverse.
Print Assumptions word_reverse_inverse.
Print Assumptions disabled_control_identity.
Print Assumptions enabled_control_action.
Print Assumptions controlled_composition.
Print Assumptions signed_composition_exact.
Print Assumptions controlled_signed_label.
Print Assumptions controlled_signed_phase.
Print Assumptions controlled_signed_disabled_identity.
Print Assumptions controlled_signed_composition.
Print Assumptions signed_word_label_projection.
Print Assumptions signed_xor_fixed_zero_label_identity.
Print Assumptions signed_word_fixed_zero_label_identity.
Print Assumptions diagonal_phase_preserves_labels.
Print Assumptions diagonal_phase_is_nontrivial.
Print Assumptions diagonal_control_relative_phase.
Print Assumptions n21_fixes_origin.
Print Assumptions n21_moves_one.
Print Assumptions n21_nonaffine.
Print Assumptions n21_excludes_signed_xor_words.
