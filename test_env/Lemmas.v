Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Tactiques.
Require Import Utf8.


(* Exercices logiques*)

Lemma exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).

Proof.
Let's fix values : A,B,C.
Let's prove the equivalance : (((A /\ B) -> C) <-> ( A -> (B -> C))).
Let's prove : ((A /\ B -> C) -> A -> B -> C).
Assume H : (A /\ B -> C).
Assume H1: A.
Assume H2: B.
Let's apply our hypothesis H.
Let's prove the conjunction : (A /\ B).
Let's apply our hypothesis H1.
Let's apply our hypothesis H2.
Assume H : (A -> B -> C ).
Assume H1: (A /\ B).
Let's apply our hypothesis H.
Let's apply our hypothesis H0.
Let's apply our hypothesis H1.
Qed.
 





Theorem direct_Inclusion_verbose:
  forall {E F: Type} (f: E → F),
     ∀ A, A ⊆ Pre f (Im f A).

Proof.
Let's fix values:A,B,C,D.
By definition of Inclusion applied to : (D ⊆ Pre C (Im C D)).
Let's fix :H.
Assume H1 : (H ∈ D).
By definition of Inverse image applied to :( H ∈ Pre C (Im C D)).
By definition of In applied to :(H ∈ (λ x : A, C x ∈ Im C D)).
By definition of Image applied to :(Im C D (C H)).
Let's show that H fit.
Let's prove the conjunction: (H ∈ D ∧ C H = C H).
Let's apply our hypothesis H1.
It is trivial.
Qed.



Theorem reverse_inclusion_verbose :
  forall {E F: Type} (f: E -> F),
    Injective f -> 
      forall A, Incl (Pre f (Im f A)) A.

Proof.
Let's fix values: A,B,C.
Assume H0 : (Injective C).
Let's fix :D.
By definition of Inclusion applied to : (Pre C (Im C D) ⊆ D).
Let's fix :E.
Assume H : (E ∈ Pre C (Im C D)).
By definition of Inverse image applied to the hypothesis H.
By definition of In applied to the hypothesis H.
By definition of Image applied to the hypothesis H.
Let's simplify our hypothesis : H.
Let's apply our hypothesis H0 on the hypothesis H1.
Let's rewrite: H1.
Let's apply our hypothesis H.
Qed.









