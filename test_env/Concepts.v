Require Import Utf8.

(* Set definition *)
(* In this file, a set is represented by its 
characteristic function. *)
Definition Ens {E : Type} := E -> Prop.
Definition In {E : Type} (A :@Ens E) (x:E) := A x.
Notation "x ∈ A" := (In A x) (at level 60).
Local Hint Unfold In.

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

Theorem exercise_inj_inter : forall  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
   (Im f (A ∩ B)) == ((Im f A) ∩ (Im f B)).
Proof.
intros.
unfold Set_eq.
split.
intros x Hx.
unfold Im in Hx.
simpl in Hx.
Abort.



(*
Theorem direct_Inclusion :
  forall {E F: Type} (f: E → F),
    ∀ A, A ⊆ pre f (Im f A).
Proof.
  intros E F f A. (* This automatically introduces four universal quantifiers, calling E, F, f and A the introduced objects. *)
  unfold Incl.    (* Unfold the definition of Inclusion. This is possible by matching A and B in the definition with A and pre (Im A). *)
  intros x Hx.    (* introduction of universal quantifier and implication *)
  unfold pre.     (* unfolding the definition of pre. *)
  unfold In.      (* unfolding the definition of In. *)
  unfold Im.      (* unfolding the definition of Image *)
  exists x.       (* introduction of existential quantifier *)
  split; trivial. (* introduction of conjunction and resolving trivial goals *)
Qed.

Theorem reverse_Inclusion :
  forall {E F: Type} (f: E -> F),
    injective f -> 
      forall A, Incl (pre f (Im f A)) A.
Proof.
  intros.                     (* introduction of universal quantifiers and of implication *)
  unfold Incl.                (* unfolding the definition of Inclusion *)
  intros.                     (* introduction of universal quantifiers and of implication *)
  unfold pre, In in H0.       (* unfolding the definition of Preimage in hypothesis H0 *)
  unfold Im in H0.            (* unfolding the definition of Image in hypothesis H0 *)
  destruct H0 as [x1 [Hx1 Heq]].      (* elimination of conjuction and of existential quantifier in H0 *)
  apply H in Heq.              (* unfolding the definition of injectivity in hypothesis H3 *)
  rewrite Heq.                 (* rewrite H3 in the conclusion *)
  assumption.                 (* resolve a trivial goal *)
Qed.





*)