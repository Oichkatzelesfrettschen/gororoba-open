(** Four-state work matrices retain the Pauli module's complex and basis types.
    MathComp storage uses column vectors in order 00,01,10,11. *)
From Stdlib Require Import Reals List Bool Lra FunctionalExtensionality.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import BranchSignedCoherence.
Import matrix.
Local Open Scope R_scope.
Definition work_basis_number basis := match basis with ket00 => 0%nat | ket01 => 1%nat | ket10 => 2%nat | ket11 => 3%nat end.
Definition work_basis_index (basis : Basis) : fintype.ordinal 4.
Proof. refine (@fintype.Ordinal 4 (work_basis_number basis) _). destruct basis; reflexivity. Defined.
Definition work_basis_decode (index : fintype.ordinal 4) : Basis :=
  match fintype.nat_of_ord index with 0%nat => ket00 | 1%nat => ket01 | 2%nat => ket10 | _ => ket11 end.
Lemma work_basis_decode_encode : forall basis, work_basis_decode (work_basis_index basis) = basis.
Proof. destruct basis; reflexivity. Qed.
Lemma work_basis_encode_decode : forall index, work_basis_index (work_basis_decode index) = index.
Proof.
  intro index. apply fintype.ord_inj.
  destruct index as [[|[|[|[|index]]]] bound]; try discriminate; reflexivity.
Qed.
Definition work_matrix_encode (operator : BranchSignedCoherence.Matrix) : matrix.matrix Complex 4 4 :=
  @matrix.matrix_of_fun Complex 4 4 matrix.matrix_key
    (fun row column => operator (work_basis_decode row) (work_basis_decode column)).
Definition work_matrix_decode (operator : matrix.matrix Complex 4 4) : BranchSignedCoherence.Matrix :=
  fun row column => operator (work_basis_index row) (work_basis_index column).
Theorem work_matrix_round_trip : forall operator row column,
  work_matrix_decode (work_matrix_encode operator) row column = operator row column.
Proof.
  intros. unfold work_matrix_decode, work_matrix_encode.
  rewrite matrix.mxE, !work_basis_decode_encode. reflexivity.
Qed.
Theorem work_storage_round_trip : forall operator,
  work_matrix_encode (work_matrix_decode operator) = operator.
Proof.
  intro operator. apply (proj1 (matrix.matrixP _ _)). intros row column.
  unfold work_matrix_encode, work_matrix_decode. rewrite matrix.mxE, !work_basis_encode_decode. reflexivity.
Qed.
Definition work_column_encode (vector : Basis -> Complex) : matrix.matrix Complex 4 1 :=
  @matrix.matrix_of_fun Complex 4 1 matrix.matrix_key (fun row _ => vector (work_basis_decode row)).
Definition work_adjoint (operator : BranchSignedCoherence.Matrix) : BranchSignedCoherence.Matrix := fun row column => conjugate (operator column row).
Definition work_product (left right : BranchSignedCoherence.Matrix) : BranchSignedCoherence.Matrix := fun row column =>
  sum_basis (fun inner => multiply (left row inner) (right inner column)).
Definition work_vector_apply (operator : BranchSignedCoherence.Matrix) (vector : Basis -> Complex) row :=
  sum_basis (fun column => multiply (operator row column) (vector column)).
Definition work_inner (left right : Basis -> Complex) :=
  sum_basis (fun row => multiply (conjugate (left row)) (right row)).
Definition work_matrix_add (left right : BranchSignedCoherence.Matrix) : BranchSignedCoherence.Matrix := fun row column => add (left row column) (right row column).
Definition work_matrix_scale factor (operator : BranchSignedCoherence.Matrix) : BranchSignedCoherence.Matrix := fun row column => scale factor (operator row column).
Definition work_zero : BranchSignedCoherence.Matrix := fun _ _ => zero.
Definition work_basis_equal left right :=
  match left,right with ket00,ket00 | ket01,ket01 | ket10,ket10 | ket11,ket11 => true | _,_ => false end.
Definition work_identity : BranchSignedCoherence.Matrix := fun row column => if work_basis_equal row column then one else zero.
Definition work_trace (operator : BranchSignedCoherence.Matrix) := sum_basis (fun row => operator row row).

Lemma complex_add_associative : forall first second third,
  add (add first second) third = add first (add second third).
Proof. intros; apply complex_ext; unfold add; simpl; ring. Qed.
Lemma complex_add_zero : forall value, add value zero = value /\ add zero value = value.
Proof. intros; split; apply complex_ext; unfold add, zero; simpl; ring. Qed.
Lemma complex_multiply_associative : forall first second third,
  multiply (multiply first second) third = multiply first (multiply second third).
Proof. intros; apply complex_ext; unfold multiply; simpl; ring. Qed.
Lemma complex_multiply_commutative : forall first second, multiply first second = multiply second first.
Proof. intros; apply complex_ext; unfold multiply; simpl; ring. Qed.
Lemma complex_conjugate_multiply : forall first second,
  conjugate (multiply first second) = multiply (conjugate first) (conjugate second).
Proof. intros; apply complex_ext; unfold conjugate, multiply; simpl; ring. Qed.
Lemma complex_conjugate_involutive : forall value, conjugate (conjugate value) = value.
Proof. intros; apply complex_ext; unfold conjugate; simpl; ring. Qed.
Lemma complex_conjugate_add : forall first second,
  conjugate (add first second) = add (conjugate first) (conjugate second).
Proof. intros; apply complex_ext; unfold conjugate, add; simpl; ring. Qed.
Lemma work_sum_ext : forall first second,
  (forall basis, first basis = second basis) -> sum_basis first = sum_basis second.
Proof. intros first second equal. unfold sum_basis. rewrite !equal. reflexivity. Qed.
Lemma work_sum_add : forall first second,
  sum_basis (fun basis => add (first basis) (second basis)) = add (sum_basis first) (sum_basis second).
Proof. intros; apply complex_ext; unfold sum_basis, add; simpl; ring. Qed.
Lemma work_sum_scale : forall factor vector,
  sum_basis (fun basis => scale factor (vector basis)) = scale factor (sum_basis vector).
Proof. intros; apply complex_ext; unfold sum_basis, add, scale; simpl; ring. Qed.
Lemma work_sum_conjugate : forall vector,
  conjugate (sum_basis vector) = sum_basis (fun basis => conjugate (vector basis)).
Proof. intros; apply complex_ext; unfold sum_basis, add, conjugate; simpl; ring. Qed.
Lemma work_sum_multiply_left : forall value vector,
  multiply value (sum_basis vector) = sum_basis (fun basis => multiply value (vector basis)).
Proof. intros; apply complex_ext; unfold sum_basis, add, multiply; simpl; ring. Qed.
Lemma work_sum_multiply_right : forall value vector,
  multiply (sum_basis vector) value = sum_basis (fun basis => multiply (vector basis) value).
Proof. intros; apply complex_ext; unfold sum_basis, add, multiply; simpl; ring. Qed.
Lemma work_sum_swap : forall values,
  sum_basis (fun row => sum_basis (fun column => values row column)) =
  sum_basis (fun column => sum_basis (fun row => values row column)).
Proof. intros; apply complex_ext; unfold sum_basis, add; simpl; ring. Qed.
Lemma work_product_associative : forall first second third row column,
  work_product (work_product first second) third row column = work_product first (work_product second third) row column.
Proof.
  intros. unfold work_product.
  transitivity (sum_basis (fun inner => sum_basis (fun middle =>
    multiply (first row middle) (multiply (second middle inner) (third inner column))))).
  - apply work_sum_ext. intro inner. rewrite work_sum_multiply_right.
    apply work_sum_ext. intro middle. apply complex_multiply_associative.
  - rewrite work_sum_swap. apply work_sum_ext. intro middle.
    rewrite work_sum_multiply_left. reflexivity.
Qed.
Lemma work_adjoint_product : forall first second row column,
  work_adjoint (work_product first second) row column = work_product (work_adjoint second) (work_adjoint first) row column.
Proof.
  intros. unfold work_adjoint, work_product. rewrite work_sum_conjugate.
  apply work_sum_ext. intro inner. rewrite complex_conjugate_multiply. apply complex_multiply_commutative.
Qed.
Lemma work_adjoint_involutive : forall operator row column,
  work_adjoint (work_adjoint operator) row column = operator row column.
Proof. intros. apply complex_conjugate_involutive. Qed.
Lemma work_inner_adjoint : forall operator left right,
  work_inner left (work_vector_apply operator right) = work_inner (work_vector_apply (work_adjoint operator) left) right.
Proof.
  intros. unfold work_inner, work_vector_apply, work_adjoint.
  transitivity (sum_basis (fun row => sum_basis (fun column =>
    multiply (conjugate (left row)) (multiply (operator row column) (right column))))).
  - apply work_sum_ext. intro row. apply work_sum_multiply_left.
  - rewrite work_sum_swap. apply work_sum_ext. intro column.
    rewrite work_sum_conjugate, work_sum_multiply_right. apply work_sum_ext. intro row.
    rewrite complex_conjugate_multiply, complex_conjugate_involutive.
    apply complex_ext; unfold multiply, conjugate; simpl; ring.
Qed.
Print Assumptions work_matrix_round_trip.
Print Assumptions work_storage_round_trip.
Print Assumptions work_product_associative.
Print Assumptions work_inner_adjoint.

Lemma work_matrix_ext : forall left right : BranchSignedCoherence.Matrix,
  (forall row column, left row column = right row column) -> left = right.
Proof. intros left right equal. apply functional_extensionality. intro row. apply functional_extensionality. intro column. apply equal. Qed.
Lemma work_product_associative_eq : forall first second third,
  work_product (work_product first second) third = work_product first (work_product second third).
Proof. intros. apply work_matrix_ext. apply work_product_associative. Qed.
Lemma work_adjoint_product_eq : forall first second,
  work_adjoint (work_product first second) = work_product (work_adjoint second) (work_adjoint first).
Proof. intros. apply work_matrix_ext. apply work_adjoint_product. Qed.
Lemma work_adjoint_involutive_eq : forall operator, work_adjoint (work_adjoint operator) = operator.
Proof. intros. apply work_matrix_ext. apply work_adjoint_involutive. Qed.
Lemma work_vector_product : forall first second vector,
  work_vector_apply (work_product first second) vector = work_vector_apply first (work_vector_apply second vector).
Proof.
  intros. apply functional_extensionality. intro row. unfold work_vector_apply, work_product.
  transitivity (sum_basis (fun inner => sum_basis (fun middle =>
    multiply (first row middle) (multiply (second middle inner) (vector inner))))).
  - apply work_sum_ext. intro inner. rewrite work_sum_multiply_right.
    apply work_sum_ext. intro middle. apply complex_multiply_associative.
  - rewrite work_sum_swap. apply work_sum_ext. intro middle. apply eq_sym, work_sum_multiply_left.
Qed.
Lemma work_quadratic_inner : forall density vector,
  quadratic_form density vector = work_inner vector (work_vector_apply density vector).
Proof.
  intros. unfold quadratic_form, work_inner, work_vector_apply.
  apply work_sum_ext. intro row. symmetry. apply work_sum_multiply_left.
Qed.
Definition work_congruence operator density := work_product (work_product operator density) (work_adjoint operator).
Theorem work_congruence_quadratic : forall operator density vector,
  quadratic_form (work_congruence operator density) vector =
  quadratic_form density (work_vector_apply (work_adjoint operator) vector).
Proof.
  intros. rewrite !work_quadratic_inner. unfold work_congruence.
  rewrite !work_vector_product, work_inner_adjoint. reflexivity.
Qed.
Lemma work_hermitian_adjoint : forall density,
  hermitian density -> work_adjoint density = density.
Proof. intros density symmetry. apply work_matrix_ext. intros row column. symmetry. apply symmetry. Qed.
Lemma work_adjoint_hermitian : forall density,
  work_adjoint density = density -> hermitian density.
Proof. intros density equal row column. symmetry. exact (f_equal (fun operator => operator row column) equal). Qed.
Theorem work_congruence_hermitian : forall operator density,
  hermitian density -> hermitian (work_congruence operator density).
Proof.
  intros operator density symmetry. apply work_adjoint_hermitian.
  unfold work_congruence. rewrite !work_adjoint_product_eq, work_adjoint_involutive_eq,
    (work_hermitian_adjoint density symmetry), work_product_associative_eq. reflexivity.
Qed.
Theorem work_congruence_positive : forall operator density,
  positive_semidefinite density -> positive_semidefinite (work_congruence operator density).
Proof.
  intros operator density [symmetry positive]. split.
  - apply work_congruence_hermitian. exact symmetry.
  - intro vector. rewrite work_congruence_quadratic. apply positive.
Qed.
Lemma work_trace_cyclic : forall first second,
  work_trace (work_product first second) = work_trace (work_product second first).
Proof.
  intros. unfold work_trace, work_product. rewrite work_sum_swap.
  apply work_sum_ext. intro column. apply work_sum_ext. intro row. apply complex_multiply_commutative.
Qed.
Lemma work_congruence_trace : forall operator density,
  work_trace (work_congruence operator density) =
  work_trace (work_product (work_product (work_adjoint operator) operator) density).
Proof.
  intros. unfold work_congruence. rewrite work_trace_cyclic, work_product_associative_eq. reflexivity.
Qed.
Lemma work_quadratic_add : forall first second vector,
  quadratic_form (work_matrix_add first second) vector = add (quadratic_form first vector) (quadratic_form second vector).
Proof. intros; apply complex_ext; unfold quadratic_form, work_matrix_add, sum_basis, add, multiply, conjugate; simpl; ring. Qed.
Lemma work_quadratic_scale : forall factor density vector,
  quadratic_form (work_matrix_scale factor density) vector = scale factor (quadratic_form density vector).
Proof. intros; apply complex_ext; unfold quadratic_form, work_matrix_scale, sum_basis, add, multiply, conjugate, scale; simpl; ring. Qed.
Lemma work_positive_add : forall first second,
  positive_semidefinite first -> positive_semidefinite second -> positive_semidefinite (work_matrix_add first second).
Proof.
  intros first second [first_symmetry first_positive] [second_symmetry second_positive]. split.
  - intros row column. unfold work_matrix_add. rewrite first_symmetry, second_symmetry.
    symmetry. apply complex_conjugate_add.
  - intro vector. rewrite work_quadratic_add. cbn [real_part add]. specialize (first_positive vector). specialize (second_positive vector). lra.
Qed.
Lemma work_positive_scale : forall factor density,
  0 <= factor -> positive_semidefinite density -> positive_semidefinite (work_matrix_scale factor density).
Proof.
  intros factor density nonnegative [symmetry positive]. split.
  - intros row column. unfold work_matrix_scale. rewrite symmetry.
    apply complex_ext; unfold scale, conjugate; simpl; ring.
  - intro vector. rewrite work_quadratic_scale. cbn [real_part scale]. apply Rmult_le_pos; [exact nonnegative|apply positive].
Qed.
Lemma work_positive_zero : positive_semidefinite work_zero.
Proof.
  split; [intros row column; apply complex_ext; unfold work_zero, zero, conjugate; simpl; ring|]. intro vector.
  unfold quadratic_form, work_zero, sum_basis, add, multiply, zero, conjugate; simpl; ring_simplify; lra.
Qed.
Lemma work_positive_trace_nonnegative : forall density,
  positive_semidefinite density -> 0 <= real_part (work_trace density).
Proof.
  intros density [symmetry positive].
  assert (diagonal : forall selected, 0 <= real_part (density selected selected)).
  { intro selected. specialize (positive (fun basis => if work_basis_equal basis selected then one else zero)).
    destruct selected; unfold quadratic_form, work_basis_equal, sum_basis, add, multiply, conjugate, one, zero in positive; simpl in positive; nra. }
  pose proof (diagonal ket00). pose proof (diagonal ket01). pose proof (diagonal ket10). pose proof (diagonal ket11).
  unfold work_trace, sum_basis, add; simpl; lra.
Qed.
Print Assumptions work_congruence_positive.
Print Assumptions work_congruence_trace.
Print Assumptions work_positive_add.
Print Assumptions work_positive_trace_nonnegative.

Lemma work_product_add_left : forall first second third,
  work_product (work_matrix_add first second) third = work_matrix_add (work_product first third) (work_product second third).
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_product, work_matrix_add, sum_basis, add, multiply; simpl; ring. Qed.
Lemma work_product_add_right : forall first second third,
  work_product first (work_matrix_add second third) = work_matrix_add (work_product first second) (work_product first third).
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_product, work_matrix_add, sum_basis, add, multiply; simpl; ring. Qed.
Lemma work_product_scale_left : forall factor first second,
  work_product (work_matrix_scale factor first) second = work_matrix_scale factor (work_product first second).
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_product, work_matrix_scale, sum_basis, scale, add, multiply; simpl; ring. Qed.
Lemma work_product_scale_right : forall factor first second,
  work_product first (work_matrix_scale factor second) = work_matrix_scale factor (work_product first second).
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_product, work_matrix_scale, sum_basis, scale, add, multiply; simpl; ring. Qed.
Lemma work_product_zero_left : forall density, work_product work_zero density = work_zero.
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_product, work_zero, sum_basis, zero, add, multiply; simpl; ring. Qed.
Lemma work_product_zero_right : forall density, work_product density work_zero = work_zero.
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_product, work_zero, sum_basis, zero, add, multiply; simpl; ring. Qed.
Lemma work_product_identity_left : forall density, work_product work_identity density = density.
Proof. intro density; apply work_matrix_ext; intros row column; destruct row; apply complex_ext; unfold work_product, work_identity, work_basis_equal, sum_basis, zero, one, add, multiply; simpl; ring. Qed.
Lemma work_product_identity_right : forall density, work_product density work_identity = density.
Proof. intro density; apply work_matrix_ext; intros row column; destruct column; apply complex_ext; unfold work_product, work_identity, work_basis_equal, sum_basis, zero, one, add, multiply; simpl; ring. Qed.
Lemma work_trace_add : forall first second,
  work_trace (work_matrix_add first second) = add (work_trace first) (work_trace second).
Proof. intros. unfold work_trace, work_matrix_add. apply work_sum_add. Qed.
Lemma work_trace_scale : forall factor density,
  work_trace (work_matrix_scale factor density) = scale factor (work_trace density).
Proof. intros. unfold work_trace, work_matrix_scale. apply work_sum_scale. Qed.
Lemma work_trace_zero : work_trace work_zero = zero.
Proof. apply complex_ext; unfold work_trace, work_zero, sum_basis, add, zero; simpl; ring. Qed.
Lemma work_congruence_add : forall operator first second,
  work_congruence operator (work_matrix_add first second) =
  work_matrix_add (work_congruence operator first) (work_congruence operator second).
Proof. intros. unfold work_congruence. rewrite work_product_add_right, work_product_add_left. reflexivity. Qed.
Lemma work_congruence_scale : forall operator factor density,
  work_congruence operator (work_matrix_scale factor density) = work_matrix_scale factor (work_congruence operator density).
Proof. intros. unfold work_congruence. rewrite work_product_scale_right, work_product_scale_left. reflexivity. Qed.
Lemma work_congruence_zero : forall operator, work_congruence operator work_zero = work_zero.
Proof. intros. unfold work_congruence. rewrite work_product_zero_right, work_product_zero_left. reflexivity. Qed.
Definition work_matrix_sum (operators : list BranchSignedCoherence.Matrix) := fold_right work_matrix_add work_zero operators.
Lemma work_matrix_sum_positive : forall operators,
  Forall positive_semidefinite operators -> positive_semidefinite (work_matrix_sum operators).
Proof. intros operators positive; induction positive; simpl; [apply work_positive_zero|apply work_positive_add; assumption]. Qed.
Lemma work_product_sum_left : forall operators density,
  work_product (work_matrix_sum operators) density = work_matrix_sum (map (fun operator => work_product operator density) operators).
Proof. induction operators; intros; simpl; [apply work_product_zero_left|]. rewrite work_product_add_left, IHoperators. reflexivity. Qed.
Lemma work_congruence_sum : forall operator densities,
  work_congruence operator (work_matrix_sum densities) = work_matrix_sum (map (work_congruence operator) densities).
Proof. intros operator densities. induction densities; simpl; [apply work_congruence_zero|]. rewrite work_congruence_add, IHdensities. reflexivity. Qed.
Print Assumptions work_product_sum_left.
Print Assumptions work_congruence_sum.

Lemma work_matrix_add_zero : forall density,
  work_matrix_add density work_zero = density /\ work_matrix_add work_zero density = density.
Proof. intros; split; apply work_matrix_ext; intros; apply complex_ext; unfold work_matrix_add, work_zero, zero, add; simpl; ring. Qed.
Lemma work_matrix_scale_zero : forall density, work_matrix_scale 0 density = work_zero.
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_matrix_scale, work_zero, zero, scale; simpl; ring. Qed.
Lemma work_matrix_scale_one : forall density, work_matrix_scale 1 density = density.
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_matrix_scale, scale; simpl; ring. Qed.
Lemma work_matrix_scale_of_zero : forall factor, work_matrix_scale factor work_zero = work_zero.
Proof. intros; apply work_matrix_ext; intros; apply complex_ext; unfold work_matrix_scale, work_zero, zero, scale; simpl; ring. Qed.
Lemma work_adjoint_identity : work_adjoint work_identity = work_identity.
Proof. apply work_matrix_ext; intros row column; destruct row, column; apply complex_ext; unfold work_adjoint, work_identity, work_basis_equal, one, zero, conjugate; simpl; ring. Qed.

Definition work_column_decode (vector : matrix.matrix Complex 4 1) : Basis -> Complex :=
  fun basis => vector (work_basis_index basis) (@fintype.ord0 0).
Lemma work_single_column_unique : forall column : fintype.ordinal 1, column = @fintype.ord0 0.
Proof. intros column. apply fintype.ord_inj. destruct column as [[|column] bounded]; [reflexivity|discriminate]. Qed.
Theorem work_column_round_trip : forall vector basis,
  work_column_decode (work_column_encode vector) basis = vector basis.
Proof. intros. unfold work_column_decode, work_column_encode. rewrite matrix.mxE, work_basis_decode_encode. reflexivity. Qed.
Theorem work_column_storage_round_trip : forall vector,
  work_column_encode (work_column_decode vector) = vector.
Proof.
  intros vector. apply (proj1 (matrix.matrixP _ _)). intros row column.
  unfold work_column_encode, work_column_decode. rewrite matrix.mxE, work_basis_encode_decode, (work_single_column_unique column). reflexivity.
Qed.
Print Assumptions work_column_round_trip.
Print Assumptions work_column_storage_round_trip.
