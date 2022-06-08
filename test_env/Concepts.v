
Definition Injective {A B} (f : A->B) :=
 forall x y, f x = f y -> x = y.

Definition Surjective {A B} (f : A->B) :=
 forall y, exists x, f x = y.

Definition Bijective {A B} (f : A->B) :=
 exists g:B->A, (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

(*Union/Intersection/Equal*)
Parameter X:Set.
Definition relation:= X -> X -> Prop.


Inductive union : relation -> relation -> X -> X -> Prop := 
  | union_left : forall (Rl Rr : relation) (x y : X), Rl x y -> union Rl Rr x y
  | union_right : forall (Rl Rr : relation) (x y : X), Rr x y -> union Rl Rr x y.

Inductive inter : relation -> relation -> relation :=
  | inter_ax : forall (R1 R2 : relation) (x y : X), R1 x y -> R2 x y -> inter R1 R2 x y.


Definition equal : relation -> relation -> Prop := fun R1 R2 =>
  forall x y, R1 x y <-> R2 x y. 

