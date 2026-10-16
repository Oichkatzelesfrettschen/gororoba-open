From mathcomp Require boot order.
From Equations Require Import Equations.
From elpi Require Import elpi.
From HB Require Import structures.
From ExtLib.Structures Require Import Monad.

Equations predecessor (value : nat) : nat :=
predecessor 0 := 0;
predecessor (S smaller) := smaller.

Example predecessor_successor (value : nat) : predecessor (S value) = value.
Proof. exact (predecessor_equation_2 value). Qed.

Example repeated_sequence_size (count value : nat) :
  @seq.size nat (@seq.nseq nat count value) = count.
Proof. exact (@seq.size_nseq nat count value). Qed.

Elpi Command compatibility_probe.
Elpi Accumulate lp:{{ main _ :- coq.say "Elpi command executed". }}.
Elpi compatibility_probe.

HB.mixin Record Pointed (carrier : Type) := { point : carrier }.
HB.structure Definition PointedType := { carrier of Pointed carrier }.
