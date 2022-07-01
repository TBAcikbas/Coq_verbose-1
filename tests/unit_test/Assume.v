Require Import Utf8.
Require Import Reals.
Require Import Basics.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example test1 : forall n:nat, n >0 -> True.
Proof.
Fix n.
Assume that H : (n>0).
Assume for contradiction H2 : (~ True).
intuition.
Qed.

Example test2 : forall n:nat, n>0 -> True.
Proof.
Fix n.
Assume H : (n>0).
auto.
Qed.

Example test3 : forall P Q : Prop, ( ~Q -> ~ P) -> P -> Q.
Proof.
intros.
Assume for contradiction H2 : (~ Q).
apply (H H2 H0).
Qed.
