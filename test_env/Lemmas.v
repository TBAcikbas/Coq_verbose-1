Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Tactics.
Require Import Utf8.
Require Import Reals.
Require Import Basics.



(* Exercices logiques*)

Theorem exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).

Proof.
Abort.
 



Theorem direct_Inclusion_verbose:
  forall {E F: Type} (f: E → F),
     ∀ A, A ⊆ Inverse f (Image f A).

Proof.
Abort.




Theorem reverse_inclusion_verbose :
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.

Proof.
Abort.




Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).


Proof.
Abort.
(* 
Let's fix values: E,F,f,A,B.
Assume H:(Injective f).
Let's prove :( (Image f (A ∩ B) == (Image f A ∩ Image f B))) by proving :((Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) ∧ (Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).
Let's prove :(Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) by proving :( ∀ x : F, x ∈ Image f (A ∩ B) → x ∈ (Image f A ∩ Image f B)).
Let's fix:y.
Assume H1:(y ∈ Image f (A ∩ B) ).
Let's prove :(y ∈ (Image f A ∩ Image f B)) by proving :((Image f A ∩ Image f B) y).
Let's prove :((Image f A ∩ Image f B) y) by proving :(((λ y : F, ∃ x : E, x ∈ A ∧ y = f x) ∩ (λ y : F, ∃ x : E, x ∈ B ∧ y = f x)) y).
Let's prove :(((λ y0 : F, ∃ x : E, x ∈ A ∧ y0 = f x) ∩ (λ y0 : F, ∃ x : E, x ∈ B ∧ y0 = f x)) y) by proving :(y ∈ (λ y0 : F, ∃ x : E, x ∈ A ∧ y0 = f x) ∧ y ∈ (λ y0 : F, ∃ x : E, x ∈ B ∧ y0 = f x)).
Let's prove :(y ∈ (λ y0 : F, ∃ x : E, x ∈ A ∧ y0 = f x)) by proving :(∃ x : E, x ∈ A ∧ y = f x).
By definition of  :(H1) we get:(∃ x : E, x ∈ (A ∩ B) ∧ y = f x).
Let's show that x fits.
Let's prove :(x ∈ A ∧ y = f x) by proving :(A x ∧ y = f x).
By definition of  :(H0) we get :((A ∩ B) x).
By definition of  :(H0) we get :(A x).
assumption.
assumption.
Let's prove:(y ∈ (λ y0 : F, ∃ x : E, x ∈ B ∧ y0 = f x)) by proving :((λ y0 : F, ∃ x : E, x ∈ B ∧ y0 = f x) y).
Let's prove :((λ y0 : F, ∃ x : E, x ∈ B ∧ y0 = f x) y) by proving :((∃ x : E, x ∈ B ∧ y = f x)).
By definition of  :(H1) we get :(Image f (A ∩ B) y).
Let's show that x fits.
Let's prove :(x ∈ B ∧ y = f x) by proving :(x ∈ B ∧ y = f x).
By definition of  :(H0) we get:((A ∩ B) x).
assumption.
assumption.
Let's prove:((Image f A ∩ Image f B) ⊆ Image f (A ∩ B)) by proving :(∀ x : F, x ∈ (Image f A ∩ Image f B) → x ∈ Image f (A ∩ B)).
Let's fix :y.
Assume H0:(y ∈ (Image f A ∩ Image f B)).
Let's prove :(y ∈ Image f (A ∩ B)) by proving :(Image f (A ∩ B) y).
Let's prove :(Image f (A ∩ B) y) by proving :(∃ x : E, x ∈ (A ∩ B) ∧ y = f x).
By definition of  :(H0) we get:((Image f A ∩ Image f B) y).
By definition of  :(H0) we get:(∃ x : E, x ∈ A  ∧ y = f x).
By definition of  :(H1) we get:(∃ x : E, x ∈ B  ∧ y = f x).
Let's show that x fits.
Let's prove :(x ∈ (A ∩ B) ∧ y = f x) by proving :(x ∈ (A ∩ B) ∧ y = f x).
Let's prove :(x ∈ (A ∩ B)) by proving :(x ∈ A /\ x ∈ B).
assumption.
Let's rewrite :H2 as H3.
Let's apply our hypothesis H on the hypothesis H3 we get :(x =x0).
Let's rewrite our goal by using our hypothesis H3.
assumption.
assumption.
Qed.
 *)


Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
Abort.
(* 
Let's fix values : A,B,f.
Assume H0 :(∃ g : B → A, Right_Inv f g).
By definition of Surjective applied to :(Surjective f).
Let's simplify our hypothesis :H0.
Let's fix :y.
Let's show that y applied to x fit. 
Let's apply our hypothesis :H.
Qed. *)




(*Lean exos...*)


Open Scope R_scope.






Theorem example: forall (f : R → R) (u : nat → R) (x0 : R) (hu:sequence_tendsto u x0) (hf:continuous_function_at f x0),  sequence_tendsto (compose f u) (f x0).
Proof.
Abort.
(*
Let's fix values :f,u,x0.
Assume H:(sequence_tendsto u x0 ).
Assume H1:(continuous_function_at f x0).
Let's prove :(sequence_tendsto (compose f u) (f x0)) by proving :(∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (compose f u n + - f x0) <= ε).
Let's fix: eps.
Assume eps_pos:(eps > 0).
By definition of:(H1) we get:( ∀ ε : R, ε > 0 → ∃ δ : R, δ > 0 ∧ (∀ x : R, Rabs (x - x0) <= δ → Rabs (f x - f x0) <= ε)).
Let's apply our hypothesis eps on the hypothesis H1.
By definition of:H0  we get :(x > 0 ∧ (∀ x1 : R, Rabs (x1 - x0) <= x → Rabs (f x1 - f x0) <= eps)).
By definition of:H we get:( ∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n + - x0) <= ε).
Let's apply our hypothesis x on the hypothesis H .
exists x1.
Let's fix :N.
Assume H4:(N ≥ x1).
Let's apply our hypothesis (u N) on the hypothesis H2.
Let's prove :(Rabs (compose f u N + - f x0) <= eps) by proving:(Rabs (compose f u N + - f x0) < eps ∨ Rabs (compose f u N + - f x0) = eps).
Let's prove the disjunction by proving :(Rabs (compose f u N + - f x0) < eps).
assumption.
Let's prove :(Rabs (compose f u N + - f x0) <= eps) by proving:(Rabs (compose f u N + - f x0) < eps ∨ Rabs (compose f u N + - f x0) = eps).
Let's prove the disjunction by proving :( Rabs (compose f u N + - f x0) = eps).
assumption.
Let's apply our hypothesis :H3.
Let's apply our hypothesis :H4.
assumption.
assumption.
Qed.*)


Theorem test :forall (u : nat→ R) (l : R),(∀ n, u n = l) → sequence_tendsto u l.
Proof.
Abort.
(* 
Let's fix values:u,l.
Assume H0:((∀ n : nat, u n = l)).
Let's prove :(sequence_tendsto u l) by proving :(∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) <= ε).
Let's fix :eps.
Assume eps_pos :(eps >0).
Let's show that (0%nat) fits.
Let's fix:N.
Assume N_pos:(N ≥ 0).
Let's apply our hypothesis N on the hypothesis H0.
Let's prove :(Rabs (u N - u N) <= eps) by proving :(Rabs (u N - u N) < eps ∨ Rabs (u N - u N) = eps).
Let's prove the disjunction by proving :(Rabs (u N - u N) < eps).
Let's rewrite our goal by using our hypothesis Rminus_diag_eq. (*Special library function*)
Let's rewrite our goal by using our hypothesis Rabs_R0. (* Special library function*)
assumption.
trivial.
Qed.
 *)










