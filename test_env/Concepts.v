Require Import Utf8.

(* Set definition *)
(* In this file, a set is represented by its 
characteristic function. *)
Definition Ens {E : Type} := E -> Prop.
Definition In {E : Type} (A :@Ens E) (x:E) := A x.
Notation "x ∈ A" := (In A x) (at level 60).

(* Inclusion relation *)
Definition Incl {E: Type} (A B: Ens) :=
  ∀ x: E, x ∈ A → x ∈ B.
Notation "A ⊆ B" := (Incl A B) (at level 80).

Definition Union {E:Type} (A B: Ens) :=
  fun x:E => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (Union A B) (at level 90). 

Definition Inter {E:Type} (A B: Ens) :=
  fun x:E => x ∈ A /\ x ∈ B.
Notation "A ∩ B" := (Inter A B) (at level 90). 

Definition Set_eq {E: Type} (A B: @Ens E) := A ⊆ B /\ B ⊆ A.
Notation "A == B" := (Set_eq A B) (at level 90).

(* Image of a set by a function *)
Definition Im {E F: Type} (f: E → F) (A: Ens): Ens :=
  fun (y: F) => ∃ x, x ∈ A ∧ y = f x.

(* Inverse image of a set by a function *)
Definition Pre {E F: Type} (f: E → F) (B: Ens): Ens :=
  fun (x: E) => f x ∈ B.

(* Injective function *)
Definition Injective {E F: Type} (f: E -> F) :=
  ∀ (x x0: E), f x = f x0 → x = x0.

Definition Surjective {E F: Type} (f:E -> F) :=
  ∀ (y:F),∃ x:E, f x = y.


Definition Right_Inv {A B} (f : A -> B) G :=  ∀ B, f (G B) = B.
