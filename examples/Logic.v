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
Let's prove (((A ∧ B → C) → A → B → C) ∧ ((A → B → C) → A ∧ B → C)) by proving (((A ∧ B → C) → A → B → C)) and (((A → B → C) → A ∧ B → C)).
Assume H:((A ∧ B → C)).
Assume H0:A.
Assume H1:B.
By H it suffices to prove (A /\B).
Let's prove(  A ∧ B )by proving A and B.
It is trivial.
It is trivial.
Assume H:(A -> B -> C).
Assume H0:(A /\ B).
By (A → B → C) it suffices to prove A and B.
By H0 we obtain HA and HB.
It is trivial.
By H0 we obtain HA and HB.
It is trivial.
Qed.
 