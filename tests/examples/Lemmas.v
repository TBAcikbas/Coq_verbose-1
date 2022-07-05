
Require Import Utf8.
Require Import Reals.
Require Import Basics.
Require Import Lra.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.
Require Import CoqVerbose.src.Hinters.Test_zone.


(* Exercices logiques*)

Theorem exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).

Proof.
Let's fix A,B,C.
Let's prove ((A ∧ B → C) ↔ (A → B → C)) by proving (((A ∧ B → C) → A → B → C) ∧ ((A → B → C) → A ∧ B → C)).
Assume H:((A ∧ B → C)).
Assume H0:A.
Assume H1:B.
Let's apply H.
Let's prove (A /\ B) by proving (A /\ B).
It is trivial.
It is trivial.
Assume H:(A -> B -> C).
Assume H0:(A /\ B).
Let's apply H.
It is trivial.
It is trivial.
Qed.
 



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
Let's prove (x ∈ A ∧ f x = f x) by proving (x ∈ A ∧ f x = f x).
It is trivial.
Let's apply f_equal.
It is trivial.
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
hnf in H1.
By H1 we obtain x0 and in_x.
By in_x we obtain H1 and H2.
Let's apply H on the hypothesis H2.
Let's rewrite the goal by using the hypothesis H2.
It is trivial.
Qed.




Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).


Proof.
Let's fix E,F,f,A,B.
Assume that H:(Injective f).
hnf.
Let's prove (Image f (A ∩ B) == (Image f A ∩ Image f B)) by proving ((Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) ∧ (Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).
Let's prove (Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) by proving ((∀ x : F, x ∈ Image f (A ∩ B) → x ∈ (Image f A ∩ Image f B))).
Let's fix x.
Assume H1:(x ∈ Image f (A ∩ B)).
Let's prove (x ∈ (Image f A ∩ Image f B)) by proving ((Image f A ∩ Image f B) x).
Let's prove ((Image f A ∩ Image f B) x) by proving (x ∈ Image f A ∧ x ∈ Image f B).
Let's prove (x ∈ Image f A) by proving (∃ x0 : E, x0 ∈ A ∧ x = f x0).
By definition of (x ∈ Image f (A ∩ B)) we get (∃ x0 : E, x0 ∈ (A ∩ B) ∧ x = f x0).
By H1 we obtain x0 and H1.
By H1 we obtain H1 and H2.
Let's prove that x0 fits.
Let's prove (x0 ∈ A ∧ x = f x0) by proving (x0 ∈ A ∧ x = f x0).
By definition of (x0 ∈ (A ∩ B)) we get ( x0 ∈ A /\ x0 ∈ B).
By H1 we obtain In_a and In_b.
It is trivial.
It is trivial.
Let's prove (x ∈ Image f B) by proving ((Image f B) x).
Let's prove ((Image f B) x) by proving  (∃ x0 : E, x0 ∈ B ∧ x = f x0).
By definition of (x ∈ Image f (A ∩ B)) we get (∃ x0 : E, x0 ∈ (A ∩ B) ∧ x = f x0).
By H1 we obtain x0 and H1.
Let's prove that x0 fits.
Let's prove (x0 ∈ B ∧ x = f x0) by proving (x0 ∈ B ∧ x = f x0).
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
Let's prove (x0 ∈ (A ∩ B) ∧ x = f x0) by proving (x0 ∈ (A ∩ B) ∧ x = f x0).
Let's prove (x0 ∈ (A ∩ B)) by proving (In A x0 /\ In B x0).
By H1 we obtain H1 and H3.
It is trivial.
By H2 we obtain H2 and H4.
By H1 we obtain H1 and H3.
By symmetry of ( x = f x1) we obtain ( f x1 =x).
Let's rewrite H4 as H3.
Let's apply  H on the hypothesis H3.
By symmetry of ( x1 = x0) we obtain ( x0 =x1).
Let's rewrite the goal by using the hypothesis H3.
It is trivial.
By H2 we obtain H2 and H4.
By H1 we obtain H1 and H3.
By symmetry of ( x = f x1) we obtain ( f x1 =x).
Let's rewrite H4 as H3.
By symmetry of (f x1 = f x0) we obtain (f x0 = f x1).
Let's rewrite the goal by using the hypothesis H3.
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
Let's prove that y applied to g fit. 
By definition of (Right_Inv f g) we get (∀ x : B, f (g x) = x).
Let's apply Hg.
Qed. 


Open Scope R_scope.

(* Theorem example: forall (f : R → R) (u : nat → R) (x0 : R) (hu:sequence_tendsto u x0) (hf:continuous_function_at f x0),  sequence_tendsto (compose f u) (f x0).
Proof.
*)



Theorem test :forall (u : nat→ R) (l : R),(∀ n, u n = l) → sequence_tendsto u l.
Proof.
Let's fix u,l.
Assume H0:((∀ n : nat, u n = l)).
Let's prove (sequence_tendsto u l) by proving (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) <= ε).
Let's fix eps.
Assume eps_pos :(eps >0).
Let's prove that (0%nat) fits.
Let's fix N.
Assume N_pos:(N ≥ 0).
Let's rewrite the goal by using the hypothesis H0.
Let's simplify.
Let's apply Rlt_le.
It is trivial.
It is trivial.
Qed.






Theorem Leanverbose_ex4  (u:nat -> R) (l:R) (hl : l > 0%R) :  sequence_tendsto u l → ∃ N, ∀ n,n ≥ N -> u n >= (l/2) .
Proof.
Assume H:(sequence_tendsto u l).
By (H (l/2) (eps2_Rgt_R0 l hl)) we obtain N and HN.
Let's prove that N fits.
Let's fix n .
Assume H0 :(n ≥ N).
Let's Assert the hypothesis T with (HN n H0) such that we get (Rabs (u n - l) <= l / 2).
Let's apply Rabs_le_le on the hypothesis T.
By T we obtain UN1 and UN2.
nra.  (*Tactics for ???? simplification ?? resolve ?? *)
Qed.


Theorem Leanverbose_ex6 ( w v u: nat -> R) (l l':R) (hu : sequence_tendsto u l) (hw : sequence_tendsto w l)
(h : ∀ n, (u n) <= (v n))
(h' : ∀ n, v n <= w n) : sequence_tendsto v l .
Proof.
Help with goal (sequence_tendsto v l).
Let's prove ( (sequence_tendsto v l) ) by proving ( (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (v n - l) <= ε) ).
Help with goal (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (v n - l) <= ε).

Let's fix  ε .
Assume  H : (ε > 0) .
Let's prove ( (∃ N : nat, ∀ n : nat, n ≥ N → Rabs (v n - l) <= ε) ) by proving (
(∃ N : nat, ∀ n : nat, n ≥ N → Rabs (v n - l) <= ε) ).

Help with hypothesis (sequence_tendsto u l).
By definition of  (ε > 0)  we get  (0 < ε) .
By definition of  R  we get  R .
By definition of  (∀ n : nat, v n <= w n)  we get  (∀ n : nat, v n <= w n) .
By definition of  (∀ n : nat, u n <= v n)  we get  (∀ n : nat, u n <= v n) .
By definition of  (sequence_tendsto w l)  we get  (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (w n - l) <= ε) .
By definition of  (sequence_tendsto u l)  we get  (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) <= ε) .
Let's Assert the hypothesis HN with (hu ε H) such that we get (∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) <= ε).
Let's Assert the hypothesis HN' with (hw ε H) such that we get (∃ N : nat, ∀ n : nat, n ≥ N → Rabs (w n - l) <= ε). 
By HN we obtain N and HN.
By HN' we obtain N' and HN'.
Let's prove that (max N N') fits.
Let's fix n.
Assume n_pos:(n ≥ Init.Nat.max N N').
By definition of ( n ≥ Init.Nat.max N N') we get (Init.Nat.max N N' ≤ n).
Let's apply ge_max_iff on the hypothesis n_pos.
By n_pos we obtain hn1 and hn2.
Let's Assert the hypothesis Hn1 with (HN n hn1) such that we get ( Rabs (u n - l) <= ε).
Let's Assert the hypothesis Hn2 with (HN' n hn2) such that we get ( Rabs (w n - l) <= ε).
Let's Assert the hypothesis h with (h n) such that we get (u n <= v n).
Let's Assert the hypothesis h' with (h' n) such that we get (v n <= w n).
Let's apply Rabs_le_le on the hypothesis Hn1.
Let's apply Rabs_le_le on the hypothesis Hn2.
By Hn1 we obtain Hn1 and Hnd.
By Hn2 we obtain Hn'1 and Hnd'.
Let's apply Rabs_le.
Let's prove (- ε <= v n - l <= ε) by proving (- ε <= v n - l <= ε).
nra.
nra.
Qed.



