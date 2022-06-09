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

Definition union {E:Type} (A B: Ens) :=
  fun x:E => x ∈ A \/ x ∈ B.

Definition inter {E:Type} (A B: Ens) :=
  fun x:E => x ∈ A /\ x ∈ B.

Definition set_eq {E: Type} (A B: @Ens E) := A ⊆ B /\ B ⊆ A.

(* Image of a set by a function *)
Definition im {E F: Type} (f: E → F) (A: Ens): Ens :=
  fun (y: F) => ∃ x, x ∈ A ∧ y = f x.

(* Inverse image of a set by a function *)
Definition pre {E F: Type} (f: E → F) (B: Ens): Ens :=
  fun (x: E) => f x ∈ B.

(* Injective function *)
Definition injective {E F: Type} (f: E -> F) :=
  ∀ (x x': E), f x = f x' → x = x'.


(*
Theorem direct_Inclusion :
  forall {E F: Type} (f: E → F),
    ∀ A, A ⊆ pre f (im f A).
Proof.
  intros E F f A. (* This automatically introduces four universal quantifiers, calling E, F, f and A the introduced objects. *)
  unfold Incl.    (* Unfold the definition of Inclusion. This is possible by matching A and B in the definition with A and pre (im A). *)
  intros x Hx.    (* introduction of universal quantifier and implication *)
  unfold pre.     (* unfolding the definition of pre. *)
  unfold In.      (* unfolding the definition of Im. *)
  unfold im.      (* unfolding the definition of Image *)
  exists x.       (* introduction of existential quantifier *)
  split; trivial. (* introduction of conjunction and resolving trivial goals *)
Qed.

Theorem reverse_Inclusion :
  forall {E F: Type} (f: E -> F),
    injective f -> 
      forall A, Incl (pre f (im f A)) A.
Proof.
  intros.                     (* introduction of universal quantifiers and of implication *)
  unfold Incl.                (* unfolding the definition of Inclusion *)
  intros.                     (* introduction of universal quantifiers and of implication *)
  unfold pre, In in H0.       (* unfolding the definition of Preimage in hypothesis H0 *)
  unfold im in H0.            (* unfolding the definition of Image in hypothesis H0 *)
  destruct H0 as [x1 [Hx1 Heq]].      (* elimination of conjuction and of existential quantifier in H0 *)
  apply H in Heq.              (* unfolding the definition of injectivity in hypothesis H3 *)
  rewrite Heq.                 (* rewrite H3 in the conclusion *)
  assumption.                 (* resolve a trivial goal *)
Qed.




Theorem exercise_inj_inter : forall  {E F: Type} (f: E -> F) (A B:Ens),
    injective f -> 
    set_eq (im f (inter A B))  (inter (im f A) (im f B)).
Proof.
intros.
unfold set_eq.
split.
intros x Hx.
unfold im in Hx.
simpl in Hx.
Abort.

*)