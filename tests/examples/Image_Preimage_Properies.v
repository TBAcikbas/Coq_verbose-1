
Require Import Utf8.
Require Import Reals.
Require Import Basics.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.
Require Import CoqVerbose.src.Hinters.Hinter3.



Theorem direct_Inclusion_verbose:
  forall {E F: Type} (f: E → F),
     ∀ A, A ⊆ Inverse f (Image f A).

Proof.
Let's fix E, F, f, A.
Let's prove  (A ⊆ Inverse f (Image f A)) by proving (∀ x : E, x ∈ A → x ∈ Inverse f (Image f A)).
Let's fix  x.
Assume H:(x ∈ A ).
Let's prove (x ∈ Inverse f (Image f A)) by proving (∃ x0 : E, x0 ∈ A ∧ f x = f x0).
Let's prove that x fits.
Let's prove the conjunction by proving (x ∈ A) and  (f x = f x).
It is trivial. 
By using reflexivity.
Qed.


Theorem reverse_inclusion_verbose :
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.

Proof.
Let's fix E,F,f.
Assume H:(Injective f).
Let's fix A.
Let's prove (Inverse f (Image f A) ⊆ A) by proving (∀ x : E, x ∈ Inverse f (Image f A) → x ∈ A).
Let's fix x.
Assume H1:(x ∈ Inverse f (Image f A)).
By definition of (x ∈ Inverse f (Image f A)) we get ( ∃ x0 : E, x0 ∈ A ∧ f x = f x0).
By H1 we obtain x0 and in_x.
By in_x we obtain H1 and H2.
(* apply H in H2. *)
By applying H on the hypothesis   (f x = f x0)  we obtain (x = x0).
By rewriting using the hypothesis (x = x0) we obtain (x0 ∈ A).
It is trivial.
Qed.




Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).


Proof.
Let's fix E,F,f,A,B.
Assume that H:(Injective f).

Let's prove (Image f (A ∩ B) == (Image f A ∩ Image f B)) by proving ((Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) ∧ (Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).
Let's prove the conjunction by proving (Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) and ((Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).
Let's prove (Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) by proving (∀ x : F, x ∈ Image f (A ∩ B) → x ∈ (Image f A ∩ Image f B)).
Let's fix x.
Assume H1:(x ∈ Image f (A ∩ B)).
Let's prove (x ∈ (Image f A ∩ Image f B)) by proving ((Image f A ∩ Image f B) x).
Let's prove the conjunction by proving (x ∈ Image f A)and  (x ∈ Image f B).

Let's prove (x ∈ Image f A) by proving (∃ x0 : E, x0 ∈ A ∧ x = f x0).
By definition of (x ∈ Image f (A ∩ B)) we get (∃ x0 : E, x0 ∈ (A ∩ B) ∧ x = f x0).
(* By H1 we obtain x0 such that HA:x0 ∈ (A ∩ B) and HB: x = f x0. *)
By H1 we obtain x0 and H1.
By H1 we obtain H1 and H2.
Let's prove that x0 fits.
Let's prove the conjunction by proving (x0 ∈ A) and  (x = f x0).
By definition of (x0 ∈ (A ∩ B)) we get ( x0 ∈ A /\ x0 ∈ B).
By H1 we obtain In_a and In_b.
It is trivial.
It is trivial.
Let's prove (x ∈ Image f B) by proving ((Image f B) x).
Let's prove ((Image f B) x) by proving  (∃ x0 : E, x0 ∈ B ∧ x = f x0).
By definition of (x ∈ Image f (A ∩ B)) we get (∃ x0 : E, x0 ∈ (A ∩ B) ∧ x = f x0).
By H1 we obtain x0 and H1.
Let's prove that x0 fits.
Let's prove the conjunction by proving (x0 ∈ B) and (x = f x0).
By H1 we obtain H1 and H2.
By definition of ( x0 ∈ (A ∩ B)) we get ( x0 ∈ A /\ x0 ∈ B).
By H1 we obtain In_a and In_b.
It is trivial.
By H1 we obtain H1 and H2.
It is trivial.
Let's prove ((Image f A ∩ Image f B) ⊆ Image f (A ∩ B)) by proving (∀ x : F, x ∈ (Image f A ∩ Image f B) → x ∈ Image f (A ∩ B)).
Let's fix x.
Assume H1:(x ∈ (Image f A ∩ Image f B)).
Let's prove ( (x ∈ Image f (A ∩ B)) ) by proving ( (∃ x0 : E, x0 ∈ (A ∩ B) ∧ x = f x0) ).
By definition of (x ∈ (Image f A ∩ Image f B)) we get( x ∈ Image f A ∧ x ∈ Image f B).
By H1 we obtain H1 and H2.
By definition of (x ∈ Image f A) we get (exists x0, (In A x0) /\  x =f x0).
By definition of (x ∈ Image f B) we get (exists x0, (In B x0) /\  x =f x0).
By H1 we obtain x0 and H1.
By H2 we obtain x1 and H2.
Let's prove that x0 fits.
Let's prove the conjunction by proving (x0 ∈ (A ∩ B)) and  (x = f x0).
Let's prove (x0 ∈ (A ∩ B)) by proving (In A x0 /\ In B x0).
Let's prove the conjunction by proving (x0 ∈ A) and  (x0 ∈ B).
By H1 we obtain H1 and H3.
It is trivial.
By H2 we obtain H2 and H4.
By H1 we obtain H1 and H3.
By symmetry , using ( x = f x1) we obtain ( f x1 =x).
Let's rewrite H4 as H3.
By applying H on the hypothesis (f x1 = f x0) we obtain (x1 =x0).
By symmetry, using  ( x1 = x0) we obtain ( x0 =x1).
By rewriting using the hypothesis (x0 = x1) we obtain (x1 ∈ B).
It is trivial.
By H2 we obtain H2 and H4.
By H1 we obtain H1 and H3.
By symmetry ,using  ( x = f x1) we obtain ( f x1 =x).
Let's rewrite H4 as H3.
By symmetry , using (f x1 = f x0) we obtain (f x0 = f x1).
By rewriting using the hypothesis ( f x0 = f x1) we obtain (x = f x1).
It is trivial.
Qed.

Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
Let's fix  A,B,f.
Assume H :(∃ g : B → A, Right_Inv f g).
By H we obtain g and Hg.
Let's prove  (Surjective f) by proving (∀ y : B, ∃ x : A, f x = y).
Let's fix y.
Let's prove that (g y) fits. 
By definition of (Right_Inv f g) we get (∀ x : B, f (g x) = x).
Let's apply Hg.
Qed. 
