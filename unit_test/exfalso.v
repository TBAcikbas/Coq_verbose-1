
Require Import Utf8.
Require Import Classical.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.



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
   We have Hc:(H2 HA) such that we get C. 
   Let's prove by exfalso.
   This is a contradiction.
- Assume HB:B.
  We have Hd:(H3 HB) such that we get D.
  It is trivial.
  Qed.