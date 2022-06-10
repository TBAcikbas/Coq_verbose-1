Require Import Utf8.
Require Import Classical.
Require Import Bool.
Require Import CoqVerbose.Concepts.




(*Tactic used to rewrite *)
Tactic Notation "Let's" "rewrite" ":" constr(H) "as" constr(H1):=
tryif (rewrite H in H1)then idtac else fail 1 "No hypothesis that can't be used to rewrite" H "as" H1.

Tactic Notation "Let's" "rewrite" ":" constr(H):=
tryif (rewrite H )then idtac else fail 1 "hypothesis" H "cannot be used to rewrite".


(*Tactic used to prove trivial cases such as 1=1 or f x = f x*)

Tactic Notation "It" "is" "trivial":=
trivial.


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


Ltac equiva_proof stmt :=
  match goal with
    |- ?Q <->  ?P => split
 |  |- ?P => fail 1 "Not an equivalence statement" (* message ??? *)  
end.


Tactic Notation "Let's" "prove" "the" "equivalance" ":" constr(stmt) :=
equiva_proof stmt.

(*Tactics used for disjonction statements *)



(*Tactics used for Conjunction statements *)


Ltac prove_conj stmt := tryif split then idtac else fail 1 "Not a conjunction".
Tactic Notation "Let's" "prove" "the" "conjunction" ": " constr(stmt) :=
prove_conj stmt.
(*by cases *) 


Ltac hyp_of_type t :=
 match goal with
 | H1:t |- _ => H1
end.

Tactic Notation "By" "cases" "on" constr(t) :=
(let H := hyp_of_type t in elim H).



(*Conclusion using the definitions and hypothesis deduce*)


Ltac spliter := repeat
match goal with
   | H:(?X1 /\ ?X2) |- _ => induction H
end.  

Ltac splits :=
 repeat
 match goal with
   | [ H : _ /\ _ |- _ ] => destruct H
end.

Ltac simpl_hyp stmt := repeat 
match goal with
   | H: _  |- _ => induction stmt 
end.  



Ltac  Applying_hypothesis hyp :=
tryif apply hyp then (tryif spliter || splits then idtac else idtac ) else fail 1 "The hypothesis used isn't:" hyp.  (* automatically use split on an hypothesis we apply *)

Tactic Notation "Let's" "apply" "our" "hypothesis" ":" constr(hyp) :=
Applying_hypothesis hyp.

Tactic Notation "Let's" "simplify" "our" "hypothesis" ":" constr(stmt) :=
simpl_hyp stmt.

Ltac  Applying_hyp_on_hyp hyp  H :=
tryif (apply hyp in H) then (tryif spliter || splits then idtac else idtac ) else fail 1 "Wrong hypothesis :" hyp.  (* automatically use split on an hypothesis we apply *)

Tactic Notation "Let's" "apply" "our" "hypothesis" constr(hyp) "on" "the" "hypothesis" constr(H):=
Applying_hyp_on_hyp hyp H.

(*Inversion statement*)

Ltac Inverting stmt := tryif inversion stmt then idtac else fail 1 "Not an induction or Coinduction".

Tactic Notation "Let's" "inverse" constr(stmt) "in" "order" "to" "induce" "properties" :=
Inverting stmt.


(*By definition ... *)

Ltac definition_unfold stmt:=
 match goal with
   |- (Incl _ _)  => unfold Incl
 | |- (In _ _) => unfold In
 | |- (Set_eq _ _) => unfold Set_eq 
end.



(*definitions applied to goals and subgoals*)
Tactic Notation "By" "definition" "of" "Inclusion" "applied" "to" ":" constr(stmt):=
tryif (unfold Incl) then idtac else fail 1 "Not an Inclusion statement".

Tactic Notation "By" "definition" "of" "Inverse" "image" "applied" "to" ":" constr(stmt):=
tryif (unfold Pre) then idtac else fail 1 "Not an Inverse image statement".

Tactic Notation "By" "definition" "of" "In" "applied" "to" ":" constr(stmt):=
tryif (unfold In) then idtac else fail 1 "Not an In statement".


Tactic Notation "By" "definition" "of" "Image" "applied" "to" ":" constr(stmt):=
tryif (unfold Im) then idtac else fail 1 "Not an Image statement".

Tactic Notation "By" "definition" "of" "equality" "applied" "to" ":" constr(stmt):=
tryif (unfold Set_eq) then idtac else fail 1 "Not an Equality statement".

Tactic Notation "By" "definition" "of" "Intersection" "applied" "to" ":" constr(stmt):=
tryif (unfold Inter) then idtac else fail 1 "Not an Intersection statement".

(*definitions applied to hypothesis*)
Tactic Notation "By" "definition" "of" "In" "applied" "to"  "the " "hypothesis" ":" constr(h):=
tryif (unfold In in h) then idtac else fail 1 "Not an In statement".

Tactic Notation "By" "definition" "of" "Inverse" "image" "applied" "to"  "the" "hypothesis" ":" constr(h):=
tryif (unfold Pre in h) then idtac else fail 1 "Not an Inverse Image statement".


Tactic Notation "By" "definition" "of"  "Image" "applied"  "to"  "the" "hypothesis" ":" constr(h):=
tryif (unfold Im in h) then idtac else fail 1 "Not an Image of statement".

Tactic Notation "By" "definition" "of" "Injective" "applied" "to" "the" "hypothesis" ":" constr(h):=
tryif (unfold Injective in h) then idtac else fail 1 "Not an Injective of statement".





Lemma surjectivity_ception: 
 forall  {A B C: Type} (f: A -> B) (g: B -> C) (x:A),
  Surjective g (f x)-> Surjective g.


