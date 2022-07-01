Require Import Utf8.
Require Import Bool.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.
Require Import CoqVerbose.src.Hinters.Hinter3.




Example test1 : forall n:nat, n >0 -> True.
Proof.
Let's fix n.
Assume H:(n>0).
intuition.
Qed.

Example test2:forall A B C:Prop,( A -> B) /\( B -> C )-> (A -> C).
Let's fix A,B,C.
tauto.
Qed.




