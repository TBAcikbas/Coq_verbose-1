
From CoqVerbose Require Import Concepts.
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
Let's apply our hypothesis H1.
Let's apply our hypothesis H2.
Assume H : (A -> B -> C ).
Assume H1: (A /\ B).
Let's apply our hypothesis H.
Let's apply our hypothesis H0.
Let's apply our hypothesis H1.
Qed.
 
Lemma Exercice_17 :forall A B,equal (inter A (union A B)) A.
Let's fix values: A,B.
Let's prove that (A) and (inter A (union A B)) is equal.                     (*No Idea how to rephrase this...*)
Assume H : (inter A (union A B) x y).
Let's inverse H in order to induce properties.
Let's apply our hypothesis H0.
Assume H : (A x y).
Let's prove the intersection (inter A (union A B) x y) by proving(A x y) and ((union A B) x y).
Let's apply our hypothesis H.
Let's prove the left side of the union : (union A B x y).
Let's apply our hypothesis H.
Qed.





