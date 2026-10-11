(** * Finite octonion incidence counts and a literal arithmetic identity.

    The octonion theorems reuse the XOR counts from
    HomotopyTransferAssociator. The theorem named
    pathion_wilmot_decomposition proves only 35 + 252 + 168 = 455.
    Its statement contains no pathion multiplication, retraction polynomial,
    or classification function. The names remain for import compatibility;
    the checked statements establish no universal transfer theorem.

    A minimal uncurved A-infinity multiplication must be associative.
    MinimalUncurvedObstruction supplies that independent obstruction.
    Finite retraction-polynomial probes require their own operation-level
    certificates before their outputs can be identified with these counts. *)

From Stdlib Require Import List Arith Bool ZArith.
Import ListNotations.
From OpenGororoba Require Import HomotopyTransferAssociator.

Theorem octonion_wilmot_u1 : fano_triple_count = 42.
Proof. exact fano_triples_are_42. Qed.

Theorem octonion_wilmot_u3 : nonfano_triple_count = 168.
Proof. exact nonfano_triples_are_168. Qed.

Theorem octonion_wilmot_total : fano_triple_count + nonfano_triple_count = 210.
Proof. exact total_triples. Qed.

Theorem octonion_wilmot_u2_empty : 210 = 42 + 0 + 168.
Proof. reflexivity. Qed.

(** Literal arithmetic, independent of any algebra or input corpus. *)
Theorem pathion_wilmot_decomposition :
  35 + 252 + 168 = 455.
Proof. reflexivity. Qed.

Print Assumptions octonion_wilmot_u1.
Print Assumptions octonion_wilmot_u3.
Print Assumptions octonion_wilmot_total.
Print Assumptions octonion_wilmot_u2_empty.
Print Assumptions pathion_wilmot_decomposition.
