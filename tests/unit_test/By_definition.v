Require Import Utf8.
Require Import Classical.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example Def_1: forall (f: nat -> nat), Injective f -> True.
intros.
(By definition of (Injective  f) we get ( ∀ x x0 : nat, f x = f x0 → x = x0)).
intuition.
Qed.

Example exfalso_ex1 : forall A B C D :Prop, 
 A \/ B -> (A-> C) -> (B->D) -> ~C -> D.
 Proof.
 Let's fix A,B,C,D .
 Assume H:(A\/B).
 Assume H2:(A->C).
 Assume H3:(B->D).
 Assume H4:(¬C).
 By cases on (A\/B).
 - Assume HA:A.
   assert (C) by (exact (H2 HA)). (* todo *)
   exfalso.
   contradiction.
- Assume HB:B.
  assert (D) by (exact (H3 HB)).
  It is trivial.
  Qed.