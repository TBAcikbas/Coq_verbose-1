Require Import Utf8.
Require Import Bool.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.
Require Import CoqVerbose.src.Hinters.Hinter3.






Example Apply_1: forall A B C: Prop, (A -> B ) -> A -> B.
Proof.
intros.
By applying H on the hypothesis A we obtain B.
trivial.
Qed.

Theorem exercice_27 : 
  forall A B C: Prop,  
    (( A -> (B -> C)) -> ((A /\ B) -> C)  ).
Proof.
intros.
By ( A -> B -> C) it suffices to prove A and B.
By H0 we obtain H1 and H2 .
trivial.
By H0 we obtain H1 and H2.
trivial.
Qed.


Theorem exercice_27_bis:
  forall A B C:Prop,
  (A -> (A -> B) -> (B->C) -> C).
  Proof.
  intros.
  By (B -> C) it suffices to prove B.
  By (A -> B) it suffices to prove A.
  assumption.
  Qed.