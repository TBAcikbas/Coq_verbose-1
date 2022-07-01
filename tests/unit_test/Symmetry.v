Require Import Utf8.
Require Import Bool.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.



Example Sym: forall (f:nat-> nat) x x0, f x =  f x0 -> x = x0.
intros.
By symmetry of (f x = f x0) we obtain (f x0 = f x).
Admitted.
