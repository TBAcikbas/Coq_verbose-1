From CoqVerbose Require Import Tactiques.

(* Exercices logiques*)

Lemma exercice_27 : forall A B C: Prop, (((A /\ B) -> C) <-> ( A -> (B -> C))).
Proof.
