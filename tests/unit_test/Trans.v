Require Import Utf8.
Require Import Classical.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example trans_succ_goal_1: forall A B C, A <= C -> C <= B -> A <= B.
Proof.
intros.
By Transitivity using C such that we get (A ≤ C) and (C ≤ B).
assumption. assumption.
Qed.



Example trans_fail_goal_1: forall A B C, A <= B -> C <= B -> B <= C.
Proof.
intros.
assert_fails By Transitivity using C such that we get (A ≤ C) and (C ≤ B).
Admitted.

