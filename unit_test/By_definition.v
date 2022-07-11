Require Import Utf8.
Require Import Classical.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example Def_1: forall (f: nat -> nat), Injective f -> True.
Proof.
intros.
By definition of (Injective  f) we get ( ∀ x x0 : nat, f x = f x0 → x = x0).
intuition.
Qed.

