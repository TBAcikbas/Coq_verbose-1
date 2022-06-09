Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Tactiques.
Require Import Utf8.


(* Exercices logiques*)

Lemma exercice_27 : forall A B C: Prop, (((A /\ B) -> C) <-> ( A -> (B -> C))).
Proof.
Let's fix values : A,B,C.
Let's prove the equivalance : (((A /\ B) -> C) <-> ( A -> (B -> C))).
Let's prove : ((A /\ B -> C) -> A -> B -> C).
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
 


Theorem direct_Inclusion_verbose:
forall {E F: Type} (f: E → F),∀ A, A ⊆ pre f (im f A).
Let's fix values:A,B,C,D.
By definition of Inclusion : (D ⊆ pre C (im C D)).
Let's fix :H.
Assume H1 : (H ∈ D).
By definition of reverse inverse applied to :( H ∈ pre C (im C D)).
By definition of In applied to :(H ∈ (λ x : A, C x ∈ im C D)).
By definition of Im applied to :(im C D (C H)).
Let's show that H fit.
By the definition of disjonction.
Let's apply our hypothesis H1.
It is trivial.
Qed.





