Require Import Utf8.
Require Import Reals.

(* Set definition *)
(* In this file, a set is represented by its 
characteristic function. *)
Definition Ens {E : Type} := E -> Prop.





Definition In {E : Type} (A :@Ens E) (x:E) := A x.
Notation "x ∈ A" := (In A x) (at level 60).

(* Inclusion relation *)
Definition Inclusion {E: Type} (A B: Ens) :=
  ∀ x: E, x ∈ A → x ∈ B.
Notation "A ⊆ B" := (Inclusion A B) (at level 80).

Definition Union {E:Type} (A B: Ens) :=
  fun x:E => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (Union A B) (at level 90). 

Definition Intersection {E:Type} (A B: Ens) :=
  fun x:E => x ∈ A /\ x ∈ B.
Notation "A ∩ B" := (Intersection A B) (at level 90). 

Definition Equal {E: Type} (A B: @Ens E) := A ⊆ B /\ B ⊆ A.
Notation "A == B" := (Equal A B) (at level 90).

(* Image of a set by a function *)
Definition Image {E F: Type} (f: E → F) (A: Ens): Ens :=
  fun (y: F) => ∃ x, x ∈ A ∧ y = f x.

(* Inverse image of a set by a function *)
Definition Inverse {E F: Type} (f: E → F) (B: Ens): Ens :=
  fun (x: E) => f x ∈ B.

(* Injective function *)
Definition Injective {E F: Type} (f: E -> F) :=
  ∀ (x x0: E), f x = f x0 → x = x0.

Definition Surjective {E F: Type} (f:E -> F) :=
  ∀ (y:F),∃ x:E, f x = y.


Definition Right_Inv {A B} (f : A -> B) G :=  ∀ x, f (G x) = x.





Open Scope R_scope.

Lemma Req_dec_1:
  forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
intros. generalize (total_order_T r1 r2) Rlt_dichotomy_converse;intuition eauto 3.
Defined.

Definition minus_eq :=forall r:R, r - r =0.

Definition continuous_function_at  (f:R -> R) (x0:R) :=
forall ε, ε > 0 -> exists δ, δ > 0  /\ forall x, Rabs (x -x0) <= δ -> Rabs( f x - f x0) <= ε.

Definition sequence_tendsto (u : nat → R) (l : R) :=
∀ ε, ε > 0 -> ∃ N, ∀ n, n ≥ N -> Rabs(u n  - l) <= ε.





Close Scope R_scope.




