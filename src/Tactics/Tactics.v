Require Import Utf8.
Require Import Classical.
Require Import Bool.
Require Import RelationClasses.
Require Import Reals.
Require Import NArith.
Require Import Basics.
Require Import CoqVerbose.src.Concepts.Concepts.
(*Verification Tactics*)


Ltac Check_goal_is  goal newgoal :=
let r := fresh in let result_goal := eval hnf in goal in
tryif cut newgoal;[intro r;exact r| idtac] then idtac else fail 1 "Error, we expect" goal "which means" result_goal "instead of" newgoal.


Ltac Check_hyp_is h stmt :=
 let Hf:=fresh in
  tryif  (assert (Hf: stmt);[exact h|idtac ];clear Hf);idtac then idtac else fail 2 "Wrong assumption, the proposition assumed shouldn't be: " stmt. 

(*sub-Tactics *)
Ltac spliter := 
match goal with
   | H:(?X1 /\ ?X2) |- _ => induction H
end.  

Ltac splits := 
repeat
 match goal with
   | [ H :context[ _ /\ _ ]|- _ ] => destruct H
end.


Ltac isconj :=
 match goal with
|  |- ?P /\ ?Q => split
|  |- _ => idtac
end.



Ltac Exists_hyp hypothesis := tryif (induction hypothesis) then idtac else idtac.


(*destruct_exist*)

Ltac destruct_exist' H P1 P := destruct H as [P1 P ].

Ltac destruct_exist'' H P2 P1 P := destruct H as [P2 P1 P].

Ltac destruct_exist''' H P3 P2 P1 P := destruct H as [P3 P2 P1 P].

Ltac destruct_exist'''' H P4 P3 P2 P1 P := destruct H as [P4 P3 P2 P1 P].


Tactic Notation "By" simple_intropattern(hyp) "we" "obtain" simple_intropattern(P) "and" simple_intropattern(P1):=
destruct_exist' hyp P P1.

Tactic Notation "By" simple_intropattern(hyp) "we" "obtain" simple_intropattern(P) "and" simple_intropattern(P1) "and" simple_intropattern(P2):=
destruct_exist'' hyp P P1 P2.

Tactic Notation "By" simple_intropattern(hyp) "we" "obtain" simple_intropattern(P) "and" simple_intropattern(P1) "and" simple_intropattern(P2) "and" simple_intropattern(P3):=
destruct_exist''' hyp P P1 P2 P3.

Tactic Notation "By" simple_intropattern(hyp) "we" "obtain" simple_intropattern(P) "and" simple_intropattern(P1) "and" simple_intropattern(P2) "and" simple_intropattern(P3) "and" simple_intropattern(P4) :=
destruct_exist'''' hyp P P1 P2 P3 P4.





(*Tactic used to rewrite *)
Tactic Notation "Let's" "rewrite"   constr(H) "as" constr(H1):=
tryif (rewrite H in H1)then idtac else tryif (symmetry in H;rewrite H in H1) then idtac else fail 1 "No hypothesis that can't be used to rewrite" H "as" H1.

Tactic Notation "Let's" "rewrite" "the" "goal" "by" "using" "the" "hypothesis"  constr(H):=
tryif (rewrite H)then idtac else fail 1 "hypothesis" H "cannot be used to rewrite".


(*Tactic used for symmety*)
Ltac Hyp_sym Hyp R :=
match goal with 
|H:Hyp |-_ => symmetry in H;Check_hyp_is H R


end.

Tactic Notation "By" "symmetry" "of " constr(Hyp) "we" "obtain" constr(Result):=
Hyp_sym Hyp Result.

(*Tactic used to prove trivial cases such as 1=1 or f x = f x*)

Tactic Notation "It" "is" "trivial":=
trivial.

(*Fix used for "forall" statements *)

Ltac Fix name :=
 match goal with
    |- ?P -> ?Q => fail 1 "Error: Let's fix is expectng a universally quantified statement of the form forall x, ...."
 |  |- forall x, ?P => intro name
end.


Tactic Notation "Let's" "fix"   simple_intropattern(X) := Fix X.

Tactic Notation "Let's" "fix"    simple_intropattern(X) "," simple_intropattern(Y) := 
Fix X;Fix Y.

Tactic Notation "Let's" "fix"     simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) := 
Fix X;Fix Y;Fix Z.

Tactic Notation "Let's" "fix"     simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) "," simple_intropattern(T) := 
Fix X;Fix Y;Fix Z;Fix T.


Tactic Notation "Let's" "fix"     simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) "," simple_intropattern(T)"," simple_intropattern(A):= 
Fix X;Fix Y;Fix Z;Fix T;Fix A.

Tactic Notation "Let's" "fix"     simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) "," simple_intropattern(T)"," simple_intropattern(A)"," simple_intropattern(M) :=
Fix X;Fix Y;Fix Z;Fix T;Fix A; Fix M.


Tactic Notation "Let's" "fix"     simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) "," simple_intropattern(T)"," simple_intropattern(A)"," simple_intropattern(M) "," simple_intropattern(R) := 
Fix X;Fix Y;Fix Z;Fix T;Fix A; Fix M; Fix R.




(*Tactic used for implications statements *)

Ltac assume_tac name stmt :=
 match goal with
   |- ?P -> ?Q => intro name;Check_hyp_is name stmt
    
end.

Ltac assume_contr_tac name stmt := apply NNPP;hnf;assume_tac name stmt.


Tactic Notation "Assume" "that" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.
Tactic Notation "Assume" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.

Tactic Notation "Assume" "for" "contradiction" simple_intropattern(I) ":" constr(H) :=
 assume_contr_tac I H.


(*Tactics used for disjonction statements *)

Ltac hyp_of_type t :=
 match goal with
 | H1:t |- _ => H1
end.

Tactic Notation "By" "cases" "on" constr(t) :=
(let H := hyp_of_type t in elim H).

Ltac disj_left_right stmt :=
match goal with
    |- stmt \/ ?Q  => left
 |  |- ?P \/ stmt  => right

end.

Tactic Notation "Let's" "prove" "the" "disjunction" "by" "proving"   constr(t):=
disj_left_right t.

(*General Apply Tactics*)
Ltac  Applying_hypothesis hyp :=
tryif apply hyp then (tryif spliter || splits then idtac else idtac ) else fail 1 "The hypothesis used isn't:" hyp.  (* automatically use split on an hypothesis we apply *)


Ltac Applying_hyp_on_hyp hyp hyp2 := 
tryif (induction (hyp hyp2)) then idtac else (tryif (apply hyp2 in hyp) then idtac else fail 1 "error cannot apply" hyp2 "to the hypothesis" hyp).


Tactic Notation "Let's" "apply"   constr(hyp) :=
Applying_hypothesis hyp.


Tactic Notation "Let's" "apply" "the" "hypothesis"  constr(hyp2) "on" "the" "hypothesis"  constr(hyp):=
Applying_hyp_on_hyp hyp hyp2 .



(*General Solving Tactics*)

Ltac prove_goal G R :=
match goal with
 |  |- ?P => hnf;Check_goal_is G R;isconj
 |  |- G => idtac

 end.




Ltac hypothesis_unfolder hyp R  :=
match goal with
| H:hyp |- _ => hnf in H;Check_hyp_is H R
| H: _ \/ _ |- _ => elim hyp




end.




Tactic Notation "Let's" "prove"   constr(Goal) "by" "proving"   constr(Result):=
prove_goal Goal Result.


Tactic Notation "By"  "definition" "of"   constr(hypothesis) "we" "get"   constr(Result):=
hypothesis_unfolder hypothesis Result.














(*


Create RewriteDb simplifications.
*)


Hint Rewrite Rminus_diag_eq : simplifications.
Hint Rewrite Rabs_R0 : simplifications.


Tactic Notation "Let's" "simplify" := autorewrite with simplifications. 





(*Tactic used for "exists" statements*)

Tactic Notation "Let's" "prove" "that" constr(witness) "works" "ie" constr(stmt) := 
 exists witness;prove_goal stmt stmt.

Tactic Notation  "Let's" "prove" "that " constr(stmt) "fits" :=
exists stmt.

Tactic Notation  "Let's" "prove" "that " constr(stmt) "applied" "to " constr(stmt_2) "fit" :=
exists (stmt_2 stmt).



(*Test_zone*)











Open Scope R_scope.

(*Lean comand: Compute ???? *)




(*  unfinished test*)


Require Import Lra.

Parameter (u v w : nat -> R) (l l':R).

Lemma Rabs_le_le: ∀ x a : R, Rabs x <= a → x <= a ∧ - a <= x.
Proof.
intros.
induction H.
apply Rabs_def2 in H.
intuition.
split.
rewrite <- H.
apply RRle_abs.
rewrite <- H.
Search Rabs.
Admitted.

Theorem Leanverbose_ex4  (u:nat -> R) (l:R) (hl : l > 0%R) :  sequence_tendsto u l → ∃ N, ∀ n,n ≥ N -> u n >= (l/2) .
Proof.
Assume H:(sequence_tendsto u l).

destruct (H (l/2) (eps2_Rgt_R0 l hl) ) as [N HN].
exists N.
intros.
assert (T:= HN n H0).
apply Rabs_le_le in T.
destruct T.
nra.
Qed.









(*
Theorem Leanverbose_ex5 ( v u:nat -> R)  (l l':R) (hu : sequence_tendsto u l) (hv : sequence_tendsto v l') :
sequence_tendsto (u + v) (l + l').
 *)

(* Theorem Leanverbose_ex6 (u: nat -> R) (hu : sequence_tendsto u l) (hw : sequence_tendsto w l)
(h : ∀ n, (u n) <= (v n))
(h' : ∀ n, v n <= w n) : sequence_tendsto v l .
hnf.
intros.
hnf in hu.
hnf in hw. 
assert (T:= hu ε H).
assert (Q:=hw ε H).
destruct T;destruct Q. *)


Close Scope R_scope.


