(** Complete retained coefficient equations, independent of curve realization. *)
From Stdlib Require Import Reals Lra Lia List ZArith.
From OpenGororoba Require Import NullityTwelveQuadraticLocus.
Import ListNotations.
Open Scope R_scope.
Definition selected_coefficients : list (nat * nat * Z) := [(30%nat,6%nat,(2)%Z);(30%nat,16%nat,(-2)%Z);(30%nat,121%nat,(2)%Z);(30%nat,132%nat,(2)%Z);(31%nat,111%nat,(-2)%Z);(31%nat,135%nat,(4)%Z);(31%nat,205%nat,(2)%Z);(33%nat,124%nat,(2)%Z);(33%nat,137%nat,(2)%Z);(33%nat,207%nat,(-2)%Z);(33%nat,223%nat,(2)%Z);(34%nat,125%nat,(2)%Z);(34%nat,136%nat,(-2)%Z);(34%nat,206%nat,(2)%Z);(34%nat,224%nat,(2)%Z);(35%nat,122%nat,(-2)%Z);(35%nat,139%nat,(-2)%Z);(35%nat,209%nat,(2)%Z);(35%nat,221%nat,(-2)%Z);(36%nat,123%nat,(-2)%Z);(36%nat,138%nat,(2)%Z);(36%nat,208%nat,(-2)%Z);(36%nat,222%nat,(-2)%Z);(38%nat,111%nat,(-2)%Z);(38%nat,135%nat,(4)%Z);(38%nat,205%nat,(2)%Z);(43%nat,6%nat,(-2)%Z);(43%nat,16%nat,(2)%Z);(43%nat,121%nat,(-2)%Z);(43%nat,132%nat,(-2)%Z);(48%nat,123%nat,(-2)%Z);(48%nat,138%nat,(2)%Z);(48%nat,208%nat,(-2)%Z);(48%nat,222%nat,(-2)%Z);(49%nat,122%nat,(2)%Z);(49%nat,139%nat,(2)%Z);(49%nat,209%nat,(-2)%Z);(49%nat,221%nat,(2)%Z);(50%nat,125%nat,(2)%Z);(50%nat,136%nat,(-2)%Z);(50%nat,206%nat,(2)%Z);(50%nat,224%nat,(2)%Z);(51%nat,124%nat,(-2)%Z);(51%nat,137%nat,(-2)%Z);(51%nat,207%nat,(2)%Z);(51%nat,223%nat,(-2)%Z);(52%nat,121%nat,(-4)%Z);(52%nat,132%nat,(-4)%Z);(53%nat,111%nat,(4)%Z);(53%nat,205%nat,(-4)%Z);(56%nat,111%nat,(4)%Z);(56%nat,205%nat,(-4)%Z);(57%nat,121%nat,(4)%Z);(57%nat,132%nat,(4)%Z)].
Definition selected_reduced_coefficients : list (nat * nat * Z) := [(0%nat,6%nat,(1)%Z);(0%nat,16%nat,(-1)%Z);(1%nat,111%nat,(1)%Z);(1%nat,205%nat,(-1)%Z);(2%nat,121%nat,(1)%Z);(2%nat,132%nat,(1)%Z);(3%nat,122%nat,(1)%Z);(3%nat,139%nat,(1)%Z);(3%nat,209%nat,(-1)%Z);(3%nat,221%nat,(1)%Z);(4%nat,123%nat,(1)%Z);(4%nat,138%nat,(-1)%Z);(4%nat,208%nat,(1)%Z);(4%nat,222%nat,(1)%Z);(5%nat,124%nat,(1)%Z);(5%nat,137%nat,(1)%Z);(5%nat,207%nat,(-1)%Z);(5%nat,223%nat,(1)%Z);(6%nat,125%nat,(1)%Z);(6%nat,136%nat,(-1)%Z);(6%nat,206%nat,(1)%Z);(6%nat,224%nat,(1)%Z);(7%nat,135%nat,(1)%Z)].
Definition selected_reconstruction_coefficients : list (nat * nat * Z) := [(30%nat,0%nat,(2)%Z);(30%nat,2%nat,(2)%Z);(31%nat,1%nat,(-2)%Z);(31%nat,7%nat,(4)%Z);(33%nat,5%nat,(2)%Z);(34%nat,6%nat,(2)%Z);(35%nat,3%nat,(-2)%Z);(36%nat,4%nat,(-2)%Z);(38%nat,1%nat,(-2)%Z);(38%nat,7%nat,(4)%Z);(43%nat,0%nat,(-2)%Z);(43%nat,2%nat,(-2)%Z);(48%nat,4%nat,(-2)%Z);(49%nat,3%nat,(2)%Z);(50%nat,6%nat,(2)%Z);(51%nat,5%nat,(-2)%Z);(52%nat,2%nat,(-4)%Z);(53%nat,1%nat,(4)%Z);(56%nat,1%nat,(4)%Z);(57%nat,2%nat,(4)%Z)].
Definition selected_monomials : list (nat * nat) := [(0%nat,0%nat);(1%nat,1%nat);(2%nat,2%nat);(3%nat,3%nat);(4%nat,4%nat);(5%nat,5%nat);(6%nat,6%nat);(7%nat,7%nat);(8%nat,8%nat);(9%nat,9%nat);(10%nat,10%nat);(11%nat,11%nat);(12%nat,12%nat);(13%nat,13%nat);(14%nat,14%nat);(15%nat,15%nat);(16%nat,16%nat);(17%nat,17%nat);(18%nat,18%nat);(19%nat,19%nat);(20%nat,20%nat);(0%nat,1%nat);(0%nat,2%nat);(0%nat,3%nat);(0%nat,4%nat);(0%nat,5%nat);(0%nat,6%nat);(0%nat,7%nat);(0%nat,8%nat);(0%nat,9%nat);(0%nat,10%nat);(0%nat,11%nat);(0%nat,12%nat);(0%nat,13%nat);(0%nat,14%nat);(0%nat,15%nat);(0%nat,16%nat);(0%nat,17%nat);(0%nat,18%nat);(0%nat,19%nat);(0%nat,20%nat);(1%nat,2%nat);(1%nat,3%nat);(1%nat,4%nat);(1%nat,5%nat);(1%nat,6%nat);(1%nat,7%nat);(1%nat,8%nat);(1%nat,9%nat);(1%nat,10%nat);(1%nat,11%nat);(1%nat,12%nat);(1%nat,13%nat);(1%nat,14%nat);(1%nat,15%nat);(1%nat,16%nat);(1%nat,17%nat);(1%nat,18%nat);(1%nat,19%nat);(1%nat,20%nat);(2%nat,3%nat);(2%nat,4%nat);(2%nat,5%nat);(2%nat,6%nat);(2%nat,7%nat);(2%nat,8%nat);(2%nat,9%nat);(2%nat,10%nat);(2%nat,11%nat);(2%nat,12%nat);(2%nat,13%nat);(2%nat,14%nat);(2%nat,15%nat);(2%nat,16%nat);(2%nat,17%nat);(2%nat,18%nat);(2%nat,19%nat);(2%nat,20%nat);(3%nat,4%nat);(3%nat,5%nat);(3%nat,6%nat);(3%nat,7%nat);(3%nat,8%nat);(3%nat,9%nat);(3%nat,10%nat);(3%nat,11%nat);(3%nat,12%nat);(3%nat,13%nat);(3%nat,14%nat);(3%nat,15%nat);(3%nat,16%nat);(3%nat,17%nat);(3%nat,18%nat);(3%nat,19%nat);(3%nat,20%nat);(4%nat,5%nat);(4%nat,6%nat);(4%nat,7%nat);(4%nat,8%nat);(4%nat,9%nat);(4%nat,10%nat);(4%nat,11%nat);(4%nat,12%nat);(4%nat,13%nat);(4%nat,14%nat);(4%nat,15%nat);(4%nat,16%nat);(4%nat,17%nat);(4%nat,18%nat);(4%nat,19%nat);(4%nat,20%nat);(5%nat,6%nat);(5%nat,7%nat);(5%nat,8%nat);(5%nat,9%nat);(5%nat,10%nat);(5%nat,11%nat);(5%nat,12%nat);(5%nat,13%nat);(5%nat,14%nat);(5%nat,15%nat);(5%nat,16%nat);(5%nat,17%nat);(5%nat,18%nat);(5%nat,19%nat);(5%nat,20%nat);(6%nat,7%nat);(6%nat,8%nat);(6%nat,9%nat);(6%nat,10%nat);(6%nat,11%nat);(6%nat,12%nat);(6%nat,13%nat);(6%nat,14%nat);(6%nat,15%nat);(6%nat,16%nat);(6%nat,17%nat);(6%nat,18%nat);(6%nat,19%nat);(6%nat,20%nat);(7%nat,8%nat);(7%nat,9%nat);(7%nat,10%nat);(7%nat,11%nat);(7%nat,12%nat);(7%nat,13%nat);(7%nat,14%nat);(7%nat,15%nat);(7%nat,16%nat);(7%nat,17%nat);(7%nat,18%nat);(7%nat,19%nat);(7%nat,20%nat);(8%nat,9%nat);(8%nat,10%nat);(8%nat,11%nat);(8%nat,12%nat);(8%nat,13%nat);(8%nat,14%nat);(8%nat,15%nat);(8%nat,16%nat);(8%nat,17%nat);(8%nat,18%nat);(8%nat,19%nat);(8%nat,20%nat);(9%nat,10%nat);(9%nat,11%nat);(9%nat,12%nat);(9%nat,13%nat);(9%nat,14%nat);(9%nat,15%nat);(9%nat,16%nat);(9%nat,17%nat);(9%nat,18%nat);(9%nat,19%nat);(9%nat,20%nat);(10%nat,11%nat);(10%nat,12%nat);(10%nat,13%nat);(10%nat,14%nat);(10%nat,15%nat);(10%nat,16%nat);(10%nat,17%nat);(10%nat,18%nat);(10%nat,19%nat);(10%nat,20%nat);(11%nat,12%nat);(11%nat,13%nat);(11%nat,14%nat);(11%nat,15%nat);(11%nat,16%nat);(11%nat,17%nat);(11%nat,18%nat);(11%nat,19%nat);(11%nat,20%nat);(12%nat,13%nat);(12%nat,14%nat);(12%nat,15%nat);(12%nat,16%nat);(12%nat,17%nat);(12%nat,18%nat);(12%nat,19%nat);(12%nat,20%nat);(13%nat,14%nat);(13%nat,15%nat);(13%nat,16%nat);(13%nat,17%nat);(13%nat,18%nat);(13%nat,19%nat);(13%nat,20%nat);(14%nat,15%nat);(14%nat,16%nat);(14%nat,17%nat);(14%nat,18%nat);(14%nat,19%nat);(14%nat,20%nat);(15%nat,16%nat);(15%nat,17%nat);(15%nat,18%nat);(15%nat,19%nat);(15%nat,20%nat);(16%nat,17%nat);(16%nat,18%nat);(16%nat,19%nat);(16%nat,20%nat);(17%nat,18%nat);(17%nat,19%nat);(17%nat,20%nat);(18%nat,19%nat);(18%nat,20%nat);(19%nat,20%nat)].

Definition sparse_integer_entry (entries : list (nat * nat * Z)) (row column : nat) : Z :=
  fold_right (fun entry total => let '(entry_row,entry_column,coefficient) := entry in
    if andb (Nat.eqb entry_row row) (Nat.eqb entry_column column)
    then (coefficient + total)%Z else total) 0%Z entries.
Definition canonical_selected_monomials : list (nat * nat) :=
  map (fun index => (index,index)) (seq 0 21) ++
  flat_map (fun monomial_left => map (fun monomial_right => (monomial_left,monomial_right))
    (seq (S monomial_left) (Nat.sub 20 monomial_left))) (seq 0 21).
Theorem selected_monomial_order : selected_monomials = canonical_selected_monomials.
Proof. vm_compute. reflexivity. Qed.
Definition selected_complete_reconstruction_check : bool :=
  forallb (fun row => forallb (fun column =>
    Z.eqb (sparse_integer_entry selected_coefficients row column)
      (fold_right (fun inner total =>
        (sparse_integer_entry selected_reconstruction_coefficients row inner *
         sparse_integer_entry selected_reduced_coefficients inner column + total)%Z)
        0%Z (seq 0 8))) (seq 0 231)) (seq 0 58).
Theorem selected_complete_coefficient_reconstruction :
  selected_complete_reconstruction_check = true.
Proof. vm_compute. reflexivity. Qed.
Definition selected_projected_row (row : nat) (z : nat -> R) : R :=
  fold_right (fun entry total => let '(entry_row,column,coefficient) := entry in
    if Nat.eqb entry_row row then
      let '(monomial_left,monomial_right) := nth column selected_monomials (0%nat,0%nat) in
      IZR coefficient * z monomial_left * z monomial_right + total else total) 0 selected_coefficients.
Definition selected_generator (index : nat) (z : nat -> R) : R :=
  match index with
  | 0%nat => (z 6%nat)^2-(z 16%nat)^2
  | 1%nat => z 5%nat*z 6%nat-z 13%nat*z 16%nat
  | 2%nat => z 13%nat*z 6%nat+z 16%nat*z 5%nat
  | 3%nat => z 17%nat*z 5%nat+z 13%nat*z 20%nat+z 16%nat*z 17%nat+z 20%nat*z 6%nat
  | 4%nat => z 13%nat*z 19%nat+z 18%nat*z 5%nat+z 16%nat*z 18%nat-z 19%nat*z 6%nat
  | 5%nat => z 19%nat*z 5%nat-z 13%nat*z 18%nat+z 16%nat*z 19%nat+z 18%nat*z 6%nat
  | 6%nat => z 13%nat*z 17%nat+z 20%nat*z 5%nat+z 16%nat*z 20%nat-z 17%nat*z 6%nat
  | 7%nat => z 16%nat*z 6%nat
  | _ => 0
  end.
Definition selected_reconstruction_row (row : nat) (z : nat -> R) : R :=
  match row with
  | 30%nat => (2) * selected_generator 0%nat z + (2) * selected_generator 2%nat z
  | 31%nat => (-2) * selected_generator 1%nat z + (4) * selected_generator 7%nat z
  | 33%nat => (2) * selected_generator 5%nat z
  | 34%nat => (2) * selected_generator 6%nat z
  | 35%nat => (-2) * selected_generator 3%nat z
  | 36%nat => (-2) * selected_generator 4%nat z
  | 38%nat => (-2) * selected_generator 1%nat z + (4) * selected_generator 7%nat z
  | 43%nat => (-2) * selected_generator 0%nat z + (-2) * selected_generator 2%nat z
  | 48%nat => (-2) * selected_generator 4%nat z
  | 49%nat => (2) * selected_generator 3%nat z
  | 50%nat => (2) * selected_generator 6%nat z
  | 51%nat => (-2) * selected_generator 5%nat z
  | 52%nat => (-4) * selected_generator 2%nat z
  | 53%nat => (4) * selected_generator 1%nat z
  | 56%nat => (4) * selected_generator 1%nat z
  | 57%nat => (4) * selected_generator 2%nat z
  | _ => 0
  end.
Theorem selected_projected_reconstruction : forall row z,
  selected_projected_row row z = selected_reconstruction_row row z.
Proof.
  intros row z. destruct row as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|row]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    cbn [selected_projected_row selected_coefficients selected_monomials
      selected_reconstruction_row selected_generator List.fold_right List.nth Nat.eqb IZR]; ring.
Qed.

Theorem selected_generators_recovered : forall z,
  selected_generator 0%nat z = selected_projected_row 30%nat z / 2 + selected_projected_row 52%nat z / 4 /\
  selected_generator 1%nat z = selected_projected_row 53%nat z / 4 /\
  selected_generator 2%nat z = - selected_projected_row 52%nat z / 4 /\
  selected_generator 3%nat z = - selected_projected_row 35%nat z / 2 /\
  selected_generator 4%nat z = - selected_projected_row 36%nat z / 2 /\
  selected_generator 5%nat z = selected_projected_row 33%nat z / 2 /\
  selected_generator 6%nat z = selected_projected_row 34%nat z / 2 /\
  selected_generator 7%nat z = selected_projected_row 31%nat z / 4 + selected_projected_row 53%nat z / 8.
Proof.
  intro z. repeat rewrite selected_projected_reconstruction.
  cbn [selected_reconstruction_row selected_generator]. repeat split; field.
Qed.
Theorem selected_projected_zero_iff_generators : forall z,
  (forall row, (row < 58)%nat -> selected_projected_row row z = 0) <->
  quadratic_common_zero (z 5%nat) (z 6%nat) (z 13%nat) (z 16%nat) (z 17%nat) (z 18%nat) (z 19%nat) (z 20%nat).
Proof.
  intro z; split.
  - intro projected_zero.
    pose proof (selected_generators_recovered z) as recovered.
    assert (p30 := projected_zero 30%nat ltac:(lia)).
    assert (p31 := projected_zero 31%nat ltac:(lia)).
    assert (p33 := projected_zero 33%nat ltac:(lia)).
    assert (p34 := projected_zero 34%nat ltac:(lia)).
    assert (p35 := projected_zero 35%nat ltac:(lia)).
    assert (p36 := projected_zero 36%nat ltac:(lia)).
    assert (p52 := projected_zero 52%nat ltac:(lia)).
    assert (p53 := projected_zero 53%nat ltac:(lia)).
    rewrite p30,p31,p33,p34,p35,p36,p52,p53 in recovered.
    cbn [selected_generator] in recovered.
    unfold quadratic_common_zero; destruct recovered as [? [? [? [? [? [? [? ?]]]]]]];
      repeat split; lra.
  - intro common_zero. unfold quadratic_common_zero in common_zero.
    destruct common_zero as [g0 [g1 [g2 [g3 [g4 [g5 [g6 g7]]]]]]].
    assert (generator_zero : forall index, selected_generator index z = 0).
    { intro index. destruct index as [|[|[|[|[|[|[|[|index]]]]]]]];
        cbn [selected_generator]; assumption || reflexivity. }
    intros row bound. rewrite selected_projected_reconstruction.
    destruct row as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|row]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn [selected_reconstruction_row]; repeat rewrite generator_zero; ring.
Qed.

Theorem selected_projected_real_zero_set : forall z,
  (forall row, (row < 58)%nat -> selected_projected_row row z = 0) <->
  coordinate_plane_a15 (z 6%nat) (z 16%nat) (z 17%nat) (z 18%nat) (z 19%nat) (z 20%nat) \/
  coordinate_plane_b17 (z 5%nat) (z 6%nat) (z 13%nat) (z 16%nat).
Proof.
  intro z. rewrite selected_projected_zero_iff_generators.
  apply selected_quadratic_zero_set.
Qed.
Print Assumptions selected_complete_coefficient_reconstruction.
Print Assumptions selected_monomial_order.
Print Assumptions selected_projected_reconstruction.
Print Assumptions selected_projected_real_zero_set.
