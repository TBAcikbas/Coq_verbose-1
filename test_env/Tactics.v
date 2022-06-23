Require Import Utf8.
Require Import Classical.
Require Import Bool.
Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Hinter.
Require Import Reals.
Require Import NArith.
Require Import Basics.


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


Ltac Applying_hyp_on_hyp hyp hyp2 R:= 
tryif (induction (hyp hyp2);Check_hyp_is hyp R) then idtac else (tryif (apply hyp2 in hyp) then idtac else fail 1 "error cannot apply" hyp2 "to the hypothesis" hyp).


Tactic Notation "Let's" "apply" "our" "hypothesis" ":" constr(hyp) :=
Applying_hypothesis hyp.


Tactic Notation "Let's" "apply" "our" "hypothesis"  constr(hyp2) "on" "the" "hypothesis"  constr(hyp) "such" "that" "we" "get" ":" constr(Result):=
Applying_hyp_on_hyp hyp hyp2 Result.



(*General Solving Tactics*)

Ltac prove_goal G R :=idtac "here";
match goal with
 |  |- ?P => Check_goal_is G R;isconj
 |  |- G => idtac
 |  |- G \/ ?Q  => left
 |  |- ?P \/ G  => right

 end.




Ltac hypothesis_unfolder hyp R  :=
match hyp with 
| ?P => hnf in hyp;Check_hyp_is hyp R;splits 
| _ \/ _ => elim hyp

end.


Tactic Notation "Let's" "prove" ":" constr(Goal) "by" "proving" ":" constr(Result):=
prove_goal Goal Result.


Tactic Notation "By" "using" "our" "definitions" "on" ":" constr(hypothesis) "such" "that" "we" "get" ":" constr(Result):=
hypothesis_unfolder hypothesis Result.


Theorem example: forall (f : R → R) (u : nat → R) (x0 : R) (hu:sequence_tendsto u x0) (hf:continuous_function_at f x0),  sequence_tendsto (compose f u) (f x0).
Proof.
Let's fix values :f,u,x0.
Assume H:(sequence_tendsto u x0 ).
Assume H1:(continuous_function_at f x0).
Let's prove :(sequence_tendsto (compose f u) (f x0)) by proving :(∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (compose f u n + - f x0) <= ε).
Let's fix: eps.
Assume eps_pos:(eps > 0).
By using our definitions on :(H1) such that we get:( ∀ ε : R, ε > 0 → ∃ δ : R, δ > 0 ∧ (∀ x : R, Rabs (x - x0) <= δ → Rabs (f x - f x0) <= ε)).
Let's apply our hypothesis eps on the hypothesis H1 such that we get:(∀ ε : R, ε > 0 → ∃ δ : R, δ > 0 ∧ (∀ x : R, Rabs (x - x0) <= δ → Rabs (f x - f x0) <= ε)).
By using our definitions on :H0  such that we get :(x > 0 ∧ (∀ x1 : R, Rabs (x1 - x0) <= x → Rabs (f x1 - f x0) <= eps)).
By using our definitions on :H such that we get:( ∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n + - x0) <= ε).
Let's apply our hypothesis x on the hypothesis H such that we get:(∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n + - x0) <= ε).
exists x1.
Let's fix :N.
Assume H4:(N ≥ x1).
induction (H2 (u N)).
unfold compose.
assumption.
Let's prove 

assumption.
induction H0.

Let's apply our hypothesis eps on the hypothesis H1 such that we get:(eps > 0 → ∃ δ : R, δ > 0 ∧ (∀ x : R, Rabs (x - x0) <= δ → Rabs (f x - f x0) <= eps)).

Abort. 
(* intros.
unfold sequence_tendsto. 
intros.
unfold continuous_function_at in hf.
assert (T:= hf ε H).
induction T as [delta [deltapos Hd]]. 
assert (X := hu delta deltapos).
destruct X as [N HN].
exists N.
intros.
assert (W:= Hd (u n)).
apply W.
apply HN.
assumption.
Qed. *)


 *)





