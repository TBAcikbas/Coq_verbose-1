Require Import Utf8.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Theorem Rewrite_succ_hyp : forall (A B C:nat), A = B -> B = C -> A = C.
Proof.
intros.
Rewrite H0 by using  H.
assumption.
Qed.

Theorem Rewrite_fail_hyp : forall (A B C D:nat),A =C -> B =D -> A = B.
Proof.
intros.
assert_fails (Rewrite H0 by using H).
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
assert_fails (By rewriting using the hypothesis  H we obtain (A = D)).
Admitted.

