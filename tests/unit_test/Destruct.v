Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example test_destruct_1: forall A B, A/\B -> B.
intros.
destruct_exist' H H H2.
assumption.
Qed.

