Require Import Utf8.
Require Import Classical.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example trans_succ_goal_1: forall A B C, A <= C -> C <= B -> A <= B.
Proof.
intros.
transitivity C.
assumption. assumption.
Qed.