Require Import Classical.
Require Import Bool.


(* repetition verbose/idtac*)

Ltac letsprove_repetition stmt :=
  match goal with
    |- stmt => idtac
  end.


Tactic Notation "Let's" "prove" ":" constr(stmt):=
letsprove_repetition stmt.

(* Pour tout/Fix*)

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

(*Il existe/Ext*)


Tactic Notation  "Let's" "show" "that " constr(stmt) "fit" :=
exists stmt.

(*supposons / assume*)

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


(* Equivalance/ double implication*)

Ltac equiva stmt :=
  match goal with
    |- ?P /\ ?Q => fail 1 "Not a A /\ A statement but a (-> and <-) statment"
 |  |- ?P \/ ?Q => fail 1 "Not a A \/ B statement but a (-> and <-) statment"
 |  |- _ <->  _ => split
 |  |- ?P => fail 1 "error" 
end.



Tactic Notation "Let's" "prove" "a" "double" "implication" "of" ":" constr(stmt) :=
equiva stmt. 

Tactic Notation "Let's" "prove" "the" "equivalance" ":" constr(stmt) :=
equiva stmt.

(*montrons que / AND* conjonction*)

Ltac conj_hyp stmt:= 
 match goal with
  |-  _ /\ _ => destruct stmt
| |- _=> fail 1 "stmt is" stmt
end.

Ltac conj_proof stmt:=
  match goal with
 |  |- stmt \/ ?Q  => left
 |  |- ?P \/ stmt  => right
  |- _ => fail 1 " To prove a conjuntion A /\ B, you need to first prove A then B or vise versa" 

  |    |- _ /\ _ => split
end.

Tactic Notation "Let's" "break" "down" "the" "hypothetic" "conjonction" constr(stmt):=
conj_hyp stmt.


Tactic Notation "Let's" "prove" "the" "conjonction"  "by" "splitting" ":" constr(stmt):=
conj_proof stmt.



(*by cases *) 


Ltac hyp_of_type t :=
 match goal with
| H1:t |- _ => H1
  end.

Tactic Notation "By" "cases" "on" constr(t) :=
(let H := hyp_of_type t in elim H).

(*Not*)

Ltac reverse stmt :=
 match goal with 
  |- _=> intro stmt
end.


Tactic Notation "Not" constr(stmt):=
reverse stmt.

(*On conclut que*)
Tactic Notation "Let's" "apply" "our" "hypothesis" constr(hyp) := apply hyp.


Lemma exercice_27 : forall A B C: Prop, (((A /\ B) -> C) <-> ( A -> (B -> C))).
Proof.
Let's fix values : A,B,C.
Let's prove the equivalance : (((A /\ B) -> C) <-> ( A -> (B -> C))).
Assume H : (A /\ B -> C).
Assume H1: A.
Assume H2: B.
Let's apply our hypothesis H.

Let's prove the conjonction by splitting : (A /\ B).










