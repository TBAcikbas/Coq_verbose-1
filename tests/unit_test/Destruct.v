Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example test_destruct_1: forall A B, A/\B -> B.
intros.
By H we obtain H1 and H2.
assumption.
Qed.




