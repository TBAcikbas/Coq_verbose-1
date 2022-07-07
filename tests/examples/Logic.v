Require Import Utf8.
Require Import Reals.
Require Import Basics.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.
Require Import CoqVerbose.src.Hinters.Hinter3.


Theorem exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).

Proof.
Let's fix A,B,C.
Let's prove ((A ∧ B → C) ↔ (A → B → C)) by proving (((A ∧ B → C) → A → B → C) ∧ ((A → B → C) → A ∧ B → C)).
Let's prove the conjunction by proving (((A ∧ B → C) → A → B → C)) and (((A → B → C) → A ∧ B → C)).
Assume H:((A ∧ B → C)).
Assume H0:A.
Assume H1:B.
Let's apply H.
Let's prove the conjunction by proving A and B.
It is trivial.
It is trivial.
Assume H:(A -> B -> C).
Assume H0:(A /\ B).
Let's apply H.
It is trivial.
It is trivial.
Qed.
 