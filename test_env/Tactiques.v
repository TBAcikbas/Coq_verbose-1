Require Import Utf8.
Require Import Classical.
Require Import Bool.
Require Import CoqVerbose.Concepts.



(*Tactic used for symmetry*)



Tactic Notation "Let's" "apply" "symmetry" "to" ":":=
tryif (symmetry) then idtac else fail 1 "this statement doesn't have a symmetry".

Tactic Notation "Let's" "apply" "symmetry" "to"  "the" "hypothesis" ":" constr(H):=
tryif (symmetry in H) then idtac else fail 1 "this statement doesn't have a symmetry".


(*Tactic used to rewrite *)
Tactic Notation "Let's" "rewrite"  constr(H) "as" constr(H1):=
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

Tactic Notation  "Let's" "show" "that " constr(stmt) "applied" "to " constr(stmt_2) "fit" :=
exists (stmt_2 stmt).


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
 |  |- ?P => fail 1 "Not an equivalence statement"  
end.


Tactic Notation "Let's" "prove" "the" "equivalence" ":" constr(stmt) :=
equiva_proof stmt.

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

(*Tactics used for Conjunction statements *)


Ltac prove_conj stmt := tryif split then idtac else fail 1 "Not a conjunction".

Tactic Notation "Let's" "prove" "the" "conjunction" ": " constr(stmt) :=
prove_conj stmt.



(* automatically use split on an hypothesis we apply *)


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
   | H: _  |- _ => tryif induction stmt then idtac else fail "The hypothesis cannot be simplified further" 
end.  


Ltac  Applying_hypothesis hyp :=
tryif apply hyp then (tryif spliter || splits then idtac else idtac ) else fail 1 "The hypothesis used isn't:" hyp.  (* automatically use split on an hypothesis we apply *)


Ltac Applying_hyp_on_hyp hyp h:= 
match goal with
 |H: _  |- _ => tryif (induction (hyp H)) then idtac else (tryif (apply h in hyp) then idtac else fail 1 "error cannot apply" h "to the hypothesis" hyp)
end.

Tactic Notation "Let's" "apply" "our" "hypothesis" ":" constr(hyp) :=
Applying_hypothesis hyp.

Tactic Notation "Let's" "simplify" "our" "hypothesis" ":" constr(stmt) :=
simpl_hyp stmt.

Tactic Notation "Let's" "apply" "our" "hypothesis" constr(H) "on" "the" "hypothesis" constr(hyp):=
Applying_hyp_on_hyp hyp H.



(*By definition ... *)
(* 
(*definitions applied to goals and subgoals*)
Tactic Notation "By" "definition" "of" "Inclusion" "applied" "to" ":" constr(stmt):=
tryif (unfold Incl) then idtac else fail 1 "Not an Inclusion statement".

<<<<<<< HEAD
Tactic Notation "By" "definition" "of" "Inverse" "applied" "to" ":" constr(stmt):=
=======
Tactic Notation "By" "definition" "of" "Inverse" "Image" "applied" "to" ":" constr(stmt):=
>>>>>>> 11d73473db319e28788be881f5ef09705401fa72
tryif (unfold Pre) then idtac else fail 1 "Not an Inverse image statement".

Tactic Notation "By" "definition" "of" "In" "applied" "to" ":" constr(stmt):=
tryif (unfold In) then idtac else fail 1 "Not an In statement".


Tactic Notation "By" "definition" "of" "Image" "applied" "to" ":" constr(stmt):=
tryif (unfold Im) then idtac else fail 1 "Not an Image statement".

Tactic Notation "By" "definition" "of" "Equality" "applied" "to" ":" constr(stmt):=
tryif (unfold Set_eq) then idtac else fail 1 "Not an Equality statement".

Tactic Notation "By" "definition" "of" "Intersection" "applied" "to" ":" constr(stmt):=
tryif (unfold Inter) then idtac else fail 1 "Not an Intersection statement".

Tactic Notation "By" "definition" "of" "Injective" "applied" "to"  ":" constr(h):=
tryif (unfold Injective) then idtac else fail 1 "Not an Injective of statement".

Tactic Notation "By" "definition" "of" "Surjective" "applied" "to"  ":" constr(h):=
tryif (unfold Surjective ) then idtac else fail 1 "Not an Surjective of statement".

Tactic Notation "By" "definition" "of" "Right" "inverse" "applied" "to" ":" constr(h):=
tryif (unfold Right_Inv) then idtac else fail 1 "Not an Right Inverse of statement".

(*utiliser des variables*)


(*definitions applied to hypothesis*)
Tactic Notation "By" "definition" "of" "Inclusion" "applied" "to" "the" "hypothesis" ":" constr(h):=
tryif (unfold Incl in h) then idtac else fail 1 "Not an Inclusion statement".


Tactic Notation "By" "definition" "of" "In" "applied" "to"  "the " "hypothesis" ":" constr(h):=
tryif (unfold In in h) then idtac else fail 1 "Not an In hypothesis".

Tactic Notation "By" "definition" "of" "Inverse" "Image" "applied" "to"  "the" "hypothesis" ":" constr(h):=
tryif (unfold Pre in h) then idtac else fail 1 "Not an Inverse Image hypothesis".


Tactic Notation "By" "definition" "of"  "Image" "applied"  "to"  "the" "hypothesis" ":" constr(h):=
tryif (unfold Im in h) then idtac else fail 1 "Not an Image of hypothesis".

Tactic Notation "By" "definition" "of" "Injective" "applied" "to" "the" "hypothesis" ":" constr(h):=
tryif (unfold Injective in h) then idtac else fail 1 "Not an Injective of hypothesis".

Tactic Notation "By" "definition" "of" "Surjective" "applied" "to" "the" "hypothesis" ":" constr(h):=
tryif (unfold Surjective in h) then idtac else fail 1 "Not an Surjective of hypothesis".


Tactic Notation "By" "definition" "of" "Right" "Inverse" "applied" "to" "the" "hypothesis" ":" constr(h):=
tryif (unfold Right_Inv in h) then idtac else fail 1 "Not an Right Inverse of hypothesis".

 *)

Tactic Notation "By" "definition" "of" constr(definition) "applied" "to" ":" constr(h):=
tryif (unfold definition) then idtac else fail 1 "Not an Right Inverse of hypothesis".


Tactic Notation "By" "definition" "of" constr(definition) "applied" "to" "the" "hypothesis" ":" constr(hypothesis):=
tryif (unfold definition in hypothesis ) then idtac else fail 1 "Not an Right Inverse of hypothesis".




Theorem Surjective_incl: forall {E F} (f:E -> F)  B ,Surjective f -> forall C, (C ⊆ B -> Set_eq (Im f (Pre f C))  C).
intros.
unfold Set_eq.
Let's prove the conjunction :((Im f (Pre f C) ⊆ C) ∧ C ⊆ Im f (Pre f C)).
By definition of Inclusion applied to:(Im f (Pre f C) ⊆ C).
Let's fix :A.
Assume H1:(A ∈ Im f (Pre f C) ).
By definition of In applied to:(A ∈ C).
Let's simplify our hypothesis :H1.
By definition of In applied to the hypothesis :H1.
By definition of Inverse Image applied to the hypothesis : H1 (*to get : (f x ∈ C)*).
By definition of In applied to the hypothesis :H1.
Let's apply symmetry to the hypothesis :H2.
Let's rewrite H2 as H1.
It is trivial.
By definition of Inclusion applied to:(C ⊆ Im f (Pre f C)).
Let's fix :A.
Assume H1:(A ∈ C).
By definition of In applied to :(A ∈ Im f (Pre f C)).
By definition of Inverse Image applied to : (Im f (Pre f C) A).
By definition of Image applied to :(Im f (λ x : E, f x ∈ C) A).
By definition of In applied to the hypothesis :H1.
By definition of Surjective applied to the hypothesis: H.
(* Let's apply our hypothesis A on the hypothesis H. *) (*inverser les aplication  dans les tac.. uni > cas part*)
induction (H A). (*Verbose pas utiliser induction sauf cas recurrence*)
Let's show that x fit.
unfold In.
Let's prove the conjunction:(C (f x) ∧ A = f x).
Let's apply symmetry to the hypothesis :H2.
rewrite H2 in H1.
assumption.
symmetry in H2.
assumption.
Qed.

(*temoin de l'existanciel*)





