Require Import Utf8.
Require Import Reals.
Require Import Basics.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example test_by_cases_1 : forall P Q : Prop, P -> Q \/ P.
Proof.
intros.
Let's prove the disjunction by proving P.
assumption.
Qed.



Example test_disj_2 : forall P Q : Prop, Q -> Q \/ P.
Proof.
Fix P.
Fix Q.
Assume H: (Q).
Let's prove the disjunction by proving Q.
assumption.
Qed.


Example test_disj_sub_1 : forall P Q K : Prop, K -> (Q\/ K) \/ P.
Proof.
Fix P.
Fix Q.
Fix K.
Assume H: (K).
disj_left_right (Q \/ K).
disj_left_right K.
assumption.
Qed.


Example test_disj_sub_2 : forall P Q K : Prop, K -> Q \/ (P\/K).
Proof.
Fix P.
Fix Q.
Fix K.
Assume H: (K).
disj_left_right (P\/K).
disj_left_right K.
assumption.
Qed.


