From CoqVerbose Require Import Tactiques.

(* Exercices logiques*)

Lemma exercice_27 : forall A B C: Prop, (((A /\ B) -> C) <-> ( A -> (B -> C))).
Proof.
Let's fix values : A,B,C.
Let's prove the equivalance : (((A /\ B) -> C) <-> ( A -> (B -> C))).
Assume H : (A /\ B -> C).
Assume H1: A.
Assume H2: B.
Let's apply our hypothesis H.
Let's prove the conjonction by splitting : (A /\ B). (* error work with "\/" for some reason ...*)

Let's apply our hypothesis H1.
Let's apply our hypothesis H2.
Assume H : (A -> B -> C ).
Assume H1: (A /\ B).
Let's break down the hypothetic conjonction H1.
Let's apply our hypothesis H.
Let's apply our hypothesis H0.
Let's apply our hypothesis H1.
Qed.

