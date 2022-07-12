Require Import Utf8.
Require Import Reals.
Require Import Basics.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example test1 : forall n:nat, n >0 -> True.
Proof.
Fix n.
Assume  H : (n>0).
Assume for contradiction H2 : (~ True).
intuition.
Qed.

Example test2 : forall n:nat, n>0 -> True.
Proof.
Fix n.
Assume H : (n>0000).
auto.
Qed.

Example test3 : forall P Q : Prop, ( ~Q -> ~ P) -> P -> Q.
Proof.
intros.
Assume for contradiction H2 : (~ Q).
apply (H H2 H0).
Qed.


Example test4: forall P Q : Prop, Q/\P -> P.
Proof.
intros P Q.
Assume HQ:Q and HP:P.
assumption.
Qed.


Example test5_fail : forall  Q T:Prop, Q/\T -> T.
Proof.
intros Q T.
assert_fails (Assume HQ:T and HT: Q).
tauto.
Qed.



Example test6 : forall P Q:Prop, P /\ ~P -> ~Q.
Proof.
Let's fix P, Q.
Assume H:P and H2:(~P).
Assume HQ:(Q).
tauto.
Qed.



Example test7 : forall P Q:Prop, P ->  ~P -> ~Q.
Proof.
Let's fix P, Q.
Assume H:P and H2:(~P).
Assume HQ:(Q).
tauto.
Qed.




Example test8 : forall P Q R S:Prop, (P /\ Q) -> (R /\ S) -> R.
Proof.
Let's fix P, Q, R, S.
Assume H:(P ) and H2:(Q).
Assume HR:R and HS:S.
assumption.
Qed.

