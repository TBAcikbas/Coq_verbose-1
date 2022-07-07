Require Import Utf8.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Theorem Rewrite_succ_hyp : forall (A B C:nat), A = B -> B = C -> A = C.
Proof.
intros.
Let's rewrite H0 as H.
assumption.
Qed.

Theorem Rewrite_fail_hyp : forall (A B C D:nat),A =C -> B =D -> A = B.
Proof.
intros.
assert_fails (Let's rewrite H0 as H).
Admitted.



Theorem Rewrite_succ_goal: forall (A B C:nat), B = A -> A = C -> B = C .
Proof.
intros.
By rewriting using the hypothesis (B =A) we obtain (A=C).
assumption.
Qed.



Theorem Rewrite_fail_goal : forall (A B C D:nat),A =C -> B =D .
Proof.
intros.
Print assert_fails.
assert_fails (Let's rewrite the goal by using the hypothesis H).
Admitted.

