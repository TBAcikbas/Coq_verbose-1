Require Import Utf8.
Require Import Bool.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.
Require Import CoqVerbose.src.Hinters.Hinter3.


Example Apply_1: forall A B C: Prop, (A -> B ) -> A -> B.
Proof.
intros.
By applying H on the hypothesis A we obtain B.
trivial.
Qed.