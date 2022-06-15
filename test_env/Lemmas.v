Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Tactiques.
Require Import Utf8.
Require Import CoqVerbose.Hinter.


(* Exercices logiques*)

Theorem exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).

Proof.
Let's fix values : A,B,C.
Let's prove the equivalence : (((A /\ B) -> C) <-> ( A -> (B -> C))).
Let's prove : ((A /\ B -> C) -> A -> B -> C).
Assume H : (A /\ B -> C).
Assume H1: A.
Assume H2: B.
Let's apply our hypothesis :H.
Let's prove the conjunction : (A /\ B).
Let's apply our hypothesis :H1.
Let's apply our hypothesis :H2.
Assume H : (A -> B -> C ).
Assume H1: (A /\ B).
Let's apply our hypothesis :H.
Let's apply our hypothesis :H0.
Let's apply our hypothesis :H1.
Qed.
 



Theorem direct_Inclusion_verbose:
  forall {E F: Type} (f: E → F),
     ∀ A, A ⊆ Inverse f (Image f A).

Proof.
Let's fix values:A,B,C,D.
By definition of Inclusion applied to : (D ⊆ Inverse C (Image C D)).
Let's fix :H.
Assume H1 : (H ∈ D).
By definition of Inverse image applied to :( H ∈ Inverse C (Image C D)).
By definition of In applied to :(H ∈ (λ x : A, C x ∈ Image C D)).
By definition of Image applied to :(Image C D (C H)).
Let's show that H fit.
Let's prove the conjunction: (H ∈ D ∧ C H = C H).
Let's apply our hypothesis :H1.
It is trivial.
Qed.



Theorem reverse_inclusion_verbose :
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.

Proof.
Let's fix values: A,B,C.
Assume H0 : (Injective C).
By definition of Inclusion applied to : (∀ A0 : Ens, Inverse C (Image C A0) ⊆ A0).
Let's fix values :D,E.
Assume H1:(E ∈ Inverse C (Image C D)).
By definition of Injective applied to the hypothesis :H0.
By definition of In applied to the hypothesis :H1.
By definition of Inverse image applied to the hypothesis :H1.
By definition of In applied to the hypothesis :H1.
By definition of Image applied to the hypothesis :H1.
Let's simplify our hypothesis :H1.
Let's simplify our hypothesis :H.
Let's apply our hypothesis H0 on the hypothesis H1.
Let's rewrite : H1.
Let's apply our hypothesis :H.
Qed.



Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).
Proof.
Let's fix values: A,B,C,D,E.
Assume H:(Injective C).
By definition of Equality applied to :(Image C (D ∩ E) == (Image C D ∩ Image C E)).
Let's prove the conjunction :((Image C (D ∩ E) ⊆ (Image C D ∩ Image C E)) ∧ (Image C D ∩ Image C E) ⊆ Image C (D ∩ E)).
By definition of Inclusion applied to : (Image C (D ∩ E) ⊆ (Image C D ∩ Image C E)).
Let's fix :F.
Assume H1: (F ∈ Image C (D ∩ E)).
Let's simplify our hypothesis : H1.
Let's simplify our hypothesis : H0.
By definition of Image applied to :((Image C D ∩ Image C E) F).
By definition of Intersection applied to :(F ∈ ((λ y : B, ∃ x0 : A, x0 ∈ D ∧ y = C x0) ∩ (λ y : B, ∃ x0 : A, x0 ∈ E ∧ y = C x0))).
By definition of Inclusion applied to :(F ∈ ((λ y : B, ∃ x0 : A, x0 ∈ D ∧ y = C x0) ∩ (λ y : B, ∃ x0 : A, x0 ∈ E ∧ y = C x0))).
Let's prove the conjunction :((∃ x0 : A, D x0 ∧ F = C x0) ∧ (∃ x0 : A, E x0 ∧ F = C x0)).
Let's show that x fit.
Let's prove the conjunction :(D x ∧ F = C x).
Let's apply our hypothesis :H0.
Let's apply our hypothesis :H1.
Let's show that x fit.
Let's prove the conjunction : (E x ∧ F = C x).
Let's apply our hypothesis :H2.
Let's apply our hypothesis :H1.
By definition of Inclusion applied to :((Image C D ∩ Image C E) ⊆ Image C (D ∩ E)).
Let's fix : F.
Assume H0: (F ∈ (Image C D ∩ Image C E)).
By definition of Image applied to : (F ∈ Image C (D ∩ E)).
By definition of Intersection applied to :( Image C (D ∩ E) F).
By definition of Image applied to :( Image C (λ x : A, x ∈ D ∧ x ∈ E) F).
By definition of In applied to: (F ∈ (λ y : B, ∃ x : A, x ∈ (λ x0 : A, x0 ∈ D ∧ x0 ∈ E) ∧ y = C x)).
By definition of Injective applied to the hypothesis : H.
Let's simplify our hypothesis :H0.
Let's simplify our hypothesis :H1.
Let's show that x fit.
Let's prove the conjunction :((D x ∧ E x) ∧ F = C x).
Let's prove the conjunction :(D x ∧ E x).
Let's apply our hypothesis :H0.
Let's rewrite :H2 as H3.
Let's apply our hypothesis H on the hypothesis H3.
Let's rewrite : H3.
Let's apply our hypothesis :H1.
Let's apply our hypothesis :H2.
Qed.



Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
Let's fix values : A,B,f.
Assume H0 :(∃ g : B → A, Right_Inv f g).
By definition of Surjective applied to :(Surjective f).
Let's simplify our hypothesis :H0.
Let's fix :y.
Let's show that y applied to x fit. 
Let's apply our hypothesis :H.
Qed.












