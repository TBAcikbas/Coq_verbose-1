Require Import Utf8.
Require Import Classical.
Require Import Bool.
Require Import RelationClasses.
Require Import Reals.
Require Import NArith.
Require Import Basics.
Require Import CoqVerbose.Concepts.

(*Verification Tactics*)


Ltac Check_goal_is  goal newgoal :=
let Hf := fresh in 
let r := fresh in
tryif cut newgoal;[intro r;exact r| idtac] then idtac else fail 1 "Wrong anwser, the result you are looking for isn't" newgoal.


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





(*Tactic used to rewrite *)
Tactic Notation "Let's" "rewrite" ":" constr(H) "as" constr(H1):=
tryif (rewrite H in H1)then idtac else tryif (symmetry in H;rewrite H in H1) then idtac else fail 1 "No hypothesis that can't be used to rewrite" H "as" H1.

Tactic Notation "Let's" "rewrite" "our" "goal" "by" "using" "our" "hypothesis"  constr(H):=
tryif (rewrite H)then idtac else fail 1 "hypothesis" H "cannot be used to rewrite".


(*Tactic used to prove trivial cases such as 1=1 or f x = f x*)

Tactic Notation "It" "is" "trivial":=
trivial.

(*Fix used for "forall" statements *)

Ltac Fix name :=
 match goal with
   |- ?P -> ?Q => fail 1 "Not a forall statement"
 |  |- forall x, ?P => intro name
end.


Tactic Notation "Let's" "fix" ":" simple_intropattern(X) := Fix X.

Tactic Notation "Let's" "fix" "values" ":" simple_intropattern(X) "," simple_intropattern(Y) := 
Fix X;Fix Y.

Tactic Notation "Let's" "fix"  "values" ":" simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) := 
Fix X;Fix Y;Fix Z.

Tactic Notation "Let's" "fix"  "values" ":" simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) "," simple_intropattern(T) := Fix X;Fix Y;Fix Z;Fix T.


Tactic Notation "Let's" "fix"  "values" ":" simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) "," simple_intropattern(T)"," simple_intropattern(A):= Fix X;Fix Y;Fix Z;Fix T;Fix A.

Tactic Notation "Let's" "fix"  "values" ":" simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) "," simple_intropattern(T)"," simple_intropattern(A)"," simple_intropattern(M) := Fix X;Fix Y;Fix Z;Fix T;Fix A; Fix M.


Tactic Notation "Let's" "fix"  "values" ":" simple_intropattern(X) "," simple_intropattern(Y) "," simple_intropattern(Z) "," simple_intropattern(T)"," simple_intropattern(A)"," simple_intropattern(M) "," simple_intropattern(R) := Fix X;Fix Y;Fix Z;Fix T;Fix A; Fix M; Fix R.




(*Tactic used for "exists" statements*)


Tactic Notation  "Let's" "show" "that " constr(stmt) "fits" :=
exists stmt.

Tactic Notation  "Let's" "show" "that " constr(stmt) "applied" "to " constr(stmt_2) "fit" :=
exists (stmt_2 stmt).


(*Tactic used for implications statements *)


Ltac assume_tac name stmt :=
 match goal with
   |- ?P -> ?Q => intro name;Check_hyp_is name stmt
    
end.

Tactic Notation "Assume" "that" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.
Tactic Notation "Assume" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.




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

Tactic Notation "Let's" "prove" "the" "disjunction" "by" "proving" ":" constr(t):=
disj_left_right t.

(*General Apply Tactics*)
Ltac  Applying_hypothesis hyp :=
tryif apply hyp then (tryif spliter || splits then idtac else idtac ) else fail 1 "The hypothesis used isn't:" hyp.  (* automatically use split on an hypothesis we apply *)


Ltac Applying_hyp_on_hyp hyp hyp2 := 
tryif (induction (hyp hyp2)) then idtac else (tryif (apply hyp2 in hyp) then idtac else fail 1 "error cannot apply" hyp2 "to the hypothesis" hyp).


Tactic Notation "Let's" "apply" "our" "hypothesis" ":" constr(hyp) :=
Applying_hypothesis hyp.


Tactic Notation "Let's" "apply" "our" "hypothesis"  constr(hyp2) "on" "the" "hypothesis"  constr(hyp):=
Applying_hyp_on_hyp hyp hyp2 .



(*General Solving Tactics*)

Ltac prove_goal G R :=
match goal with
 |  |- ?P => Check_goal_is G R;isconj
 |  |- G => idtac

 end.




Ltac hypothesis_unfolder hyp R  :=
match hyp with
| _ \/ _ => elim hyp
| _ => hnf in hyp;Check_hyp_is hyp R;splits;destruct hyp 

end.


Tactic Notation "Let's" "prove" ":" constr(Goal) "by" "proving" ":" constr(Result):=
prove_goal Goal Result.


Tactic Notation "By"  "definition" "of" ":" constr(hypothesis) "we" "get" ":" constr(Result):=
hypothesis_unfolder hypothesis Result.



Definition max_le_iff n m p := p <= max n m <-> p <= n \/ p <= m.

Open Scope R_scope.


(*Lean comand: Compute ???? *)




(*  unfinished test*)

(* 
Theorem Leanvernbove_ex3: forall (u :nat -> R) n, u n = 1 -> sequence_tendsto u 1.
intros.
unfold sequence_tendsto.
intro ε .
intro eps_pos.
exists 0%nat.
intro .
intro.
split_Rabs.
Search "transitivity".
transitivity Hlt.
apply Rlt_trans with (r1 :=(u n0 - 1)) in eps_pos.
rewrite Ropp_minus_distr'.
left.
symmetry in H.
rewrite H.
elim H0.

 *)









Theorem Leanvernbove_ex3: forall (u :nat -> R) n, u n = 1 -> sequence_tendsto u 1.
intros.
unfold sequence_tendsto.
intro ε .
intro eps_pos.
exists 0%nat.
intros.
symmetry in H.
rewrite H.
left.
Search "Rabs".

rewrite Rabs_pos.

Parameter (u v w : nat -> R) (l l':R).

(*  unfinished test*)
(* Theorem Leanverbose_ex4  (u:nat -> R) (l:R) (hl : l > 0) : sequence_tendsto u l → ∃ N, ∀ n,n ≥ N -> u n >= (l/2) .
intros.
induction (H (l/2)) .
exists x.
intros.
destruct (H0 n H1).
left.
hnf.  *)


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
destruct (hu ε H).
destruct (hw ε H).
exists (max x x0).
intros.
rewrite max_le_iff in H2.
SearchPattern (_ > _). *)



