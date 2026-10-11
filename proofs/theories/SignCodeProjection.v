(** Scalar normalization of binary sign words.

    The subspace hypotheses describe an arbitrary binary code containing
    the constant word. SchreierSignCode.v separately proves the all-order
    characterization of the Cayley-Dickson Schreier span. The Rust sign_code
    audit checks the concrete implementation independently for 2 <= n <= 8.
    Equality is pointwise, so functional extensionality is unnecessary.
    The direct sum is a binary-code statement, not a group direct product. *)

From Stdlib Require Import Bool.

Section Projection.
  Context {Index : Type} (origin : Index).
  Definition word := Index -> bool.
  Definition word_eq (left right : word) := forall index, left index = right index.
  Definition word_add (left right : word) : word := fun index => xorb (left index) (right index).
  Definition constant (value : bool) : word := fun _ => value.
  Definition project (value : word) : word :=
    word_add value (constant (value origin)).

  Theorem projection_zero : forall value, project value origin = false.
  Proof. intros value. unfold project, word_add, constant. apply xorb_nilpotent. Qed.
  Print Assumptions projection_zero.

  Theorem projection_linear : forall left right,
      word_eq (project (word_add left right))
              (word_add (project left) (project right)).
  Proof.
    intros left right index. unfold project, word_add, constant.
    destruct (left index), (right index), (left origin), (right origin); reflexivity.
  Qed.
  Print Assumptions projection_linear.

  Theorem projection_idempotent : forall value,
      word_eq (project (project value)) (project value).
  Proof.
    intros value index. unfold project, word_add, constant.
    destruct (value index), (value origin); reflexivity.
  Qed.
  Print Assumptions projection_idempotent.

  Theorem projection_kernel : forall value,
      word_eq (project value) (constant false) <->
      word_eq value (constant (value origin)).
  Proof.
    intros value. unfold word_eq, project, word_add, constant.
    split; intros equal index; specialize (equal index);
      destruct (value index), (value origin); simpl in *; congruence.
  Qed.
  Print Assumptions projection_kernel.

  Theorem scalar_decomposition : forall value,
      word_eq value (word_add (project value) (constant (value origin))).
  Proof.
    intros value index. unfold project, word_add, constant.
    destruct (value index), (value origin); reflexivity.
  Qed.
  Print Assumptions scalar_decomposition.

  Theorem scalar_decomposition_unique : forall value normalized scalar,
      normalized origin = false ->
      word_eq value (word_add normalized (constant scalar)) ->
      scalar = value origin /\ word_eq normalized (project value).
  Proof.
    intros value normalized scalar at_origin equal.
    assert (scalar_value : scalar = value origin).
    { specialize (equal origin). unfold word_add, constant in equal.
      rewrite at_origin in equal. simpl in equal. symmetry. exact equal. }
    split; [exact scalar_value |].
    intros index. unfold project, word_add, constant.
    specialize (equal index). unfold word_add, constant in equal.
    rewrite <- scalar_value, equal.
    destruct (normalized index), scalar; reflexivity.
  Qed.
  Print Assumptions scalar_decomposition_unique.

  Variable kernel_code : word -> Prop.
  Hypothesis code_extensional : forall left right,
      word_eq left right -> kernel_code left -> kernel_code right.
  Hypothesis code_zero : kernel_code (constant false).
  Hypothesis code_one : kernel_code (constant true).
  Hypothesis code_add : forall left right,
      kernel_code left -> kernel_code right -> kernel_code (word_add left right).

  Theorem projection_preserves_code : forall value,
      kernel_code value -> kernel_code (project value).
  Proof.
    intros value member. unfold project. apply code_add; [exact member |].
    destruct (value origin); assumption.
  Qed.
  Print Assumptions projection_preserves_code.

  Theorem projection_image : forall normalized,
      (exists value, kernel_code value /\ word_eq (project value) normalized) <->
      kernel_code normalized /\ normalized origin = false.
  Proof.
    intros normalized. split.
    - intros [value [member equal]]. split.
      + eapply code_extensional; [exact equal |].
        apply projection_preserves_code. exact member.
      + rewrite <- (equal origin). apply projection_zero.
    - intros [member at_origin]. exists normalized. split; [exact member |].
      intros index. unfold project, word_add, constant.
      rewrite at_origin. apply xorb_false_r.
  Qed.
  Print Assumptions projection_image.

  Theorem code_direct_sum : forall value, kernel_code value ->
      kernel_code (project value) /\ project value origin = false /\
      word_eq value (word_add (project value) (constant (value origin))) /\
      (forall normalized scalar, normalized origin = false ->
        word_eq value (word_add normalized (constant scalar)) ->
        scalar = value origin /\ word_eq normalized (project value)).
  Proof.
    intros value member. split.
    - apply projection_preserves_code. exact member.
    - split; [apply projection_zero |].
      split; [apply scalar_decomposition |].
      intros normalized scalar at_origin equal.
      exact (scalar_decomposition_unique value normalized scalar at_origin equal).
  Qed.
  Print Assumptions code_direct_sum.
End Projection.

(** Coherent control carries the removed constant as a relative phase. *)
Theorem controlled_projection_exact : forall control value scalar : bool,
    andb control value = xorb (andb control (xorb value scalar)) (andb control scalar).
Proof. intros [] [] []; reflexivity. Qed.
Print Assumptions controlled_projection_exact.

Theorem controlled_scalar_distinguishable :
    andb false false = andb false true /\
    andb true false <> andb true true.
Proof. split; [reflexivity | discriminate]. Qed.
Print Assumptions controlled_scalar_distinguishable.
