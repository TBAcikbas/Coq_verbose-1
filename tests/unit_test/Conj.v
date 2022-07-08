Require Import Utf8.
Require Import Reals.
Require Import Basics.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.



Theorem direct_Inclusion_verbose:
  forall {E F: Type} (f: E → F) ,
     ∀ A, A ⊆ Inverse f (Image f A).

Proof.
intros.
Let's prove  (A ⊆ Inverse f (Image f A)) by proving (∀ x : E, x ∈ A → x ∈ Inverse f (Image f A)).
intros.
Let's prove  (x ∈ Inverse f (Image f A)) by proving (∃ x0 : E, x0 ∈ A ∧ f x = f x0).
Let's prove that x fits.
Let's prove (x ∈ A ∧ f x = f x) by proving (x ∈ A) and ( f x = f x).
assumption.
Let's prove (f x = f x) by proving (f x = f x).
trivial.
Qed.




Theorem direct_Inclusion_verbose_fail:
  forall {E F: Type} (f: E → F) ,
     ∀ A, A ⊆ Inverse f (Image f A).

Proof.
intros;hnf;intros;exists x.
assert_fails Let's prove (x ∈ A ∧ f x = f x) by proving (x ∈ A) and (  x =  x).
Admitted.

