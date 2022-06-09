
Require Import Classical.
Require Import Bool.
Require Import CoqVerbose.Concepts.


(*Commun definition that can be used*)




(*Tactic used for repeting the current objective without causing an error*)

Ltac letsprove_repetition stmt :=
  match goal with
  |- stmt => idtac
| |- _  => fail 2 "This is not what that we need to prove !!!"
end.


Tactic Notation "Let's" "prove" ":" constr(stmt):=
letsprove_repetition stmt.

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


Tactic Notation  "Let's" "show" "that " constr(stmt) "fit" :=
exists stmt.

(*Tactic used for implications statements *)

Ltac check_hyp_is h stmt :=
 let Hf:=fresh in 

  tryif  (assert (Hf: stmt);[exact h|idtac ];clear Hf) then idtac else fail 2 "Wrong assumption, the proposition assumed shouldn't be: " stmt. 


Ltac assume_tac name stmt :=
 match goal with
   |- ?P -> ?Q => intro name;check_hyp_is name stmt
    
end.

Tactic Notation "Assume" "that" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.
Tactic Notation "Assume" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.


(* Tactic used for equivalance statements *)
(* /\ is not triggered due the existance of <-> statement ...*)

Ltac equiva_proof stmt :=
  match goal with
    |- ?P /\ ?Q => fail 1 "The equivalance is a disjunction of statement with the form of (A -> B) /\ (B -> A),However for conjunction cases we will use 'Let's apply our hypothesis [hypothesis]' " 
 |  |- ?P \/ ?Q => fail 1 "Not a disjunction Statements the equivalance is a conjunction case with the form of (A -> B) /\ (B -> A) it can also be written as <->"   
 |  |- ?Q <->  ?P => split
 |  |- ?P => fail 1 "error" (* message ??? *)  
end.


Tactic Notation "Let's" "prove" "the" "equivalance" ":" constr(stmt) :=
equiva_proof stmt.

(*Tactics used for conjonction statements *)


Ltac spliter := repeat
match goal with
   | H:(?X1 /\ ?X2) |- _ => induction H
end.  

Ltac splits :=
 repeat
 match goal with
  | |- ?x /\ ?y => split
end.

Tactic Notation "By" "the" "definition" "of" "disjonction" :=
splits.


 
(*by cases *) 


Ltac hyp_of_type t :=
 match goal with
| H1:t |- _ => H1
  end.

Tactic Notation "By" "cases" "on" constr(t) :=
(let H := hyp_of_type t in elim H).



(*Conclusion using the definitions and hypothesis deduce*)

Ltac  Applying_hypothesis hyp :=
tryif apply hyp then (tryif spliter || splits then idtac else idtac ) else fail 1 "The hypothesis used isn't:" hyp.  (* automatically use split on an hypothesis we apply *)

Tactic Notation "Let's" "apply" "our" "hypothesis" constr(hyp) :=
Applying_hypothesis hyp.

(*Inversion statement*)

Ltac Inverting stmt := tryif inversion stmt then idtac else fail 1 "Not an induction or Coinduction".

Tactic Notation "Let's" "inverse" constr(stmt) "in" "order" "to" "induce" "properties" :=
Inverting stmt.

(*Intersection statement*)
Tactic Notation "Let's" "prove" "the" "intersection" constr(stmt)"by" "proving" constr(A) "and" constr(B):= split.


(*Union Statement*)

Tactic Notation "Let's" "prove" "the" "left" "side" "of" "the" "union" ":" constr(stmt):=
apply union_left.

Tactic Notation "Let's" "prove" "the" "right" "side" "of" "the" "union" ":" constr(stmt):=
apply union_right.

(*Miscelinious/Unknown categorie*)

Tactic Notation "Let's" "prove" "that" constr(stmt1) "and" constr (stmt2) "is" "equal" := split.







