Require Import Utf8.
Require Import Classical.
Require Import Bool.
Require Import RelationClasses.
Require Import Reals.
Require Import NArith.
Require Import Basics.
Require Import Lra.
Require Import CoqVerbose.src.Concepts.Concepts.
(*Verification Tactics*)


Ltac Check_goal_is  goal newgoal :=
let r := fresh in let result_goal := eval hnf in goal in
tryif cut newgoal;[intro r;exact r| idtac] then idtac else fail 0 "Error, we expect" goal "which means" result_goal "instead of" newgoal.


Ltac Check_hyp_is h stmt :=
 let Hf:=fresh in
  tryif  (assert (Hf: stmt);[exact h|idtac ];clear Hf);idtac then idtac else fail 0 "Wrong assumption, the proposition assumed shouldn't be: " stmt. 

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


Tactic Notation "By" constr(hyp) "we" "obtain" simple_intropattern(P) "and" simple_intropattern(P1):=
destruct_exist' hyp P P1.

Tactic Notation "By" constr(hyp) "we" "obtain" simple_intropattern(P) "and" simple_intropattern(P1) "and" simple_intropattern(P2):=
destruct_exist'' hyp P P1 P2.

Tactic Notation "By" constr(hyp) "we" "obtain" simple_intropattern(P) "and" simple_intropattern(P1) "and" simple_intropattern(P2) "and" simple_intropattern(P3):=
destruct_exist''' hyp P P1 P2 P3.

Tactic Notation "By" constr(hyp) "we" "obtain" simple_intropattern(P) "and" simple_intropattern(P1) "and" simple_intropattern(P2) "and" simple_intropattern(P3) "and" simple_intropattern(P4) :=
destruct_exist'''' hyp P P1 P2 P3 P4.


(*Addding new hypothesis*)


Ltac new_hyp hyp_name hyp_contents hyp_results :=  
tryif (assert (hyp_name:=hyp_contents)) then Check_hyp_is hyp_name hyp_results else clear hyp_name.

Tactic Notation "We" "have" simple_intropattern(Hypothesis_name) ":" constr(Hypothesis_contents) "such" "that" "we" "get" constr(Hypothesis_results):=
new_hyp Hypothesis_name Hypothesis_contents Hypothesis_results.




(*Tactic used to rewrite *)
Ltac rewrite_goal Hyp new_goal :=
match goal with
|H:Hyp |- ?P => tryif (rewrite H) then Check_goal_is (H) new_goal else fail
|H:Hyp |- ?P => fail 1 "Cannot use"H ":" Hyp" to rewrite" P
end.

Tactic Notation  "Rewrite"   constr(H1) "by" "using" constr(H):=
tryif (rewrite H in H1)then idtac else tryif (symmetry in H;rewrite H in H1) then idtac else fail 0 "No hypothesis that can't be used to rewrite" H "as" H1.


Tactic Notation "By" "rewriting" "using" "the" "hypothesis"  constr(H) "we" "obtain" constr(new_goal):=
rewrite_goal H new_goal.


(*Tactic used for symmety*)
Ltac sym Hyp R :=
match goal with 
|H:Hyp |-_  => symmetry in H;Check_hyp_is H R
|H:_   |-?P => symmetry;Check_goal_is P R
end.

Tactic Notation "By" "symmetry" "," "using" constr(elem) "we" "obtain" constr(Result):=
sym elem Result.


(*Tactic used for Transitivity*)

Ltac Trans_verif middle_man split_result_l split_result_r :=tryif (transitivity middle_man) then
match goal with
|- ?P  => Check_goal_is P split_result_l + Check_goal_is P split_result_r
end
else fail 1 middle_man "cannot be used for transitivity".


Tactic Notation "By" "Transitivity" "using" constr(middle_man) "such" "that" "we" "get" constr(result_of_trans_first) "and" constr(result_of_trans_second):=
Trans_verif middle_man result_of_trans_first result_of_trans_second.


(* Tactic used for Compute*)

Tactic Notation "We" "Compute":=
first [nra| ring| field].


(*Tactic used for Contradictions*)

Tactic Notation "Let's" "prove" "by" "exfalso":=
exfalso.

Tactic Notation "This" "is" "a" "contradiction":=
contradiction.


(*Tactic used to prove trivial cases such as 1=1 or f x = f x*)

Tactic Notation "It" "is" "trivial":=
trivial.


(*Reflexivity*)

Tactic Notation "By" "using" "reflexivity":=
reflexivity.

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

Ltac assume_tac_conj name_1 stmt_1 name_2 stmt_2:=let r := fresh in  
match goal with
  |-?P /\ ?Q -> ?A =>intro r;Check_hyp_is r (stmt_1 /\ stmt_2);destruct r as [name_1 name_2]
 end.


Ltac assume_tac name stmt :=
match goal with
   |- ?P -> ?Q =>  hnf;intro name;Check_hyp_is name stmt
 |  |- ~?P => hnf;intro name;Check_hyp_is name stmt
end.


Ltac assume_contr_tac name stmt := apply NNPP;hnf;assume_tac name stmt.



 
Tactic Notation "Assume" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.

Tactic Notation "Assume" simple_intropattern(I) ":" constr(H) "and" simple_intropattern(I2) ":" constr(H2):=
tryif assume_tac_conj I H I2 H2 then idtac else ( assume_tac I H; assume_tac I2 H2).

Tactic Notation "Assume" simple_intropattern(I) ":" constr(H)  "and" simple_intropattern(I2) ":" constr(H2) "and" simple_intropattern(I3) ":" constr(H3) :=
 assume_tac I H; assume_tac I2 H2 ;assume_tac I3 H3.
 
 


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

Tactic Notation "Let's" "prove" "the" "disjunction" "by" "proving"  constr(t):=
disj_left_right t.

(*General Apply Tactics*)



Ltac  Applying_hypothesis hyp stmt := 
match goal with 
|H:hyp |- ?P => tryif (apply H) then  match goal with |-?Q => Check_goal_is Q stmt end else idtac "failed" 
|_  => tryif (apply hyp) then  match goal with |-?Q => Check_goal_is Q stmt end else idtac "failed2"
end.



Ltac  Applying_hypothesis_2 hyp stmt  stmt2:=
match hyp with
| stmt -> stmt2 -> ?P => match goal with |H:hyp |-_ => apply H end
| _                   => idtac hyp "isn't used correctly" 
end.

Ltac  Applying_hypothesis_3 hyp stmt  stmt2 stmt3 :=
match hyp with
| stmt -> stmt2 -> stmt3 -> ?P => match goal with |H:hyp |-_ => apply H end
| _                            => idtac hyp "isn't used correctly" 
end.

Ltac  Applying_hypothesis_4 hyp stmt  stmt2 stmt3 stmt4:=
match hyp with
| stmt -> stmt2 ->  stmt3 -> stmt4 -> ?P => match goal with |H:hyp |-_ => apply H end
| _                                      => idtac hyp "isn't used correctly" 
end.


Ltac Applying_hyp_on_hyp hyp hyp2 Result  := 

match goal with 
|H2:hyp2|-_  => tryif (apply hyp in H2) then Check_hyp_is H2 Result else fail 1 "wrong apply"
|H2:hyp2|- _ => fail 1 "wrong apply"
end.


Tactic Notation "By" constr(hyp) "it" "suffices" "to" "prove" constr(stmt) :=
Applying_hypothesis hyp stmt.



Tactic Notation "By" constr(hyp) "it" "suffices" "to" "prove" constr(stmt) "and" constr(stmt2):=
Applying_hypothesis_2 hyp stmt stmt2.


Tactic Notation "By" constr(hyp) "it" "suffices" "to" "prove" constr(stmt) "and" constr(stmt2) "and" constr(stmt3):=
Applying_hypothesis_3 hyp stmt stmt2 stmt3.


Tactic Notation "By" constr(hyp) "it" "suffices" "to" "prove" constr(stmt) "and" constr(stmt2) "and" constr(stmt3) "and" constr(stmt4):=
Applying_hypothesis_4 hyp stmt stmt2 stmt3 stmt4.


Tactic Notation "By" "applying" constr(hyp) "on" "the" "hypothesis"  constr(hyp2) "we" "obtain" constr(expected) :=
Applying_hyp_on_hyp hyp hyp2 expected  .


Ltac prove_equi_conj C_full C_left C_right :=
 match goal with
|  |- ?P /\ ?Q  => Check_goal_is (P /\ Q) (C_full);Check_goal_is P ( C_left /\ C_right);Check_goal_is Q (C_left /\ C_right);split 
|  |- ?P <-> ?Q => Check_goal_is (P <-> Q) (C_full);Check_goal_is P ( C_left /\ C_right);Check_goal_is Q (C_left /\ C_right);split 

end.



Tactic Notation "Let's" "prove" constr(full_stmt) "by" "proving"   constr(stmt_left) "and" constr(stmt_right):=
prove_equi_conj full_stmt stmt_left stmt_right.


(*General Solving Tactics*)

Ltac prove_goal G R :=
match goal with
|  |- ?P => hnf;Check_goal_is G R
|  |- G  => idtac

 end.




Ltac hypothesis_unfolder hyp R  :=
match goal with
| H:hyp     |- _ => hnf in H;Check_hyp_is H R
| H: _ \/ _ |- _ => elim hyp

  end.




Tactic Notation "Let's" "prove"   constr(Goal) "by" "proving"   constr(Result):=
prove_goal Goal Result.


Tactic Notation "By"  "definition" "of"   constr(hypothesis) "we" "get"   constr(Result):=
hypothesis_unfolder hypothesis Result.



(*Tactic used for "exists" statements*)

Tactic Notation "Let's" "prove" "that" constr(witness) "works" "ie" constr(stmt) := 
 exists witness;prove_goal stmt stmt.

Tactic Notation  "Let's" "prove" "that " constr(stmt) "fits" :=
exists stmt.





(*Simplification Tactics*)




Tactic Notation "Let's" "simplify" := autorewrite with simplifications. 





