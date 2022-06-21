Require Import Utf8.
Require Import Classical.
Require Import Bool.
Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Hinter.




(*Verification Tactics*)

Ltac Check_goal_is  goal newgoal :=
let Hf := fresh in 
let r := fresh in 
tryif cut newgoal;[intro r;exact r| idtac] then idtac else fail 1 "Wrong anwser, the result you are looking for isn't" newgoal.

Ltac Check_hyp_is h stmt :=
 let Hf:=fresh in 

  tryif  (assert (Hf: stmt);[exact h|idtac ];clear Hf) then idtac else fail 2 "Wrong assumption, the proposition assumed shouldn't be: " stmt. 




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


Ltac spliter := 
match goal with
   | H:(?X1 /\ ?X2) |- _ => induction H
end.  

Ltac splits :=
 repeat
 match goal with
   | [ H : _ /\ _ |- _ ] => destruct H
end.

Ltac simpl_hyp stmt :=  
match goal with
     | H: _  |- _ => tryif induction stmt then (tryif spliter || splits then idtac else idtac )  else fail "The hypothesis cannot be simplified further" 
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

Tactic Notation "Let's" "apply" "our" "hypothesis" ":" constr(hyp) "on" "the" "hypothesis" ":" constr(H):=
Applying_hyp_on_hyp H hyp.


Ltac definition_unfolder G R :=



match goal with



| [                              |- context [ _ <-> _ ]      ] => Check_goal_is G R
| [                              |- context [ _ == _ ]       ] => Check_goal_is G R
| [                              |- context [ _  ⊆ _ ]       ] => Check_goal_is G R
| [                              |- context [ _ /\ _ ]       ] => Check_goal_is G R
| [                              |- context [ _ ∩  _ ]       ] => Check_goal_is G R
| [                              |- context [ _ ∪  _ ]       ] => Check_goal_is G R
| [ H:context[_ /\ _ ]           |- _                        ] => Check_hyp_is G R
| [ H:context[exists x,?P]       |- _                        ] => Check_hyp_is G R
| [ H:context[ _ ∈ _ ]           |- _                        ] => unfold In in H;Check_hyp_is H R
| [                              |- context [?A ∈ ?B  ]      ] => Check_goal_is G R
| [                              |- context [Image _ _]      ] => Check_goal_is G R
| [                              |- context [Inverse _ _ ]   ] => Check_goal_is G R
| [                              |- context [Right_Inv _ _]  ] => Check_goal_is G R
| [ H:context[Image _  _ ]       |- _                        ] => Check_hyp_is H R
| [ H:context[_ <->  _]                  |- _                        ] =>  simpl_hyp H;Check_hyp_is H R
| [ H:context[ _  ⊆ _ ]                   |- _                        ] => unfold Inclusion in H;Check_hyp_is H R
| [ H:context[ _ ∩ _ ]                    |- _                        ] => unfold Intersection in H;Check_hyp_is H R
| [ H:context[ _ ∪ _ ]                    |- _                        ] => unfold Union in H;Check_hyp_is H R
| [                              |- Surjective _             ] => Check_goal_is G R
| [ H:Injective _                |- _                        ] => Check_hyp_is G R
| [ H:context[ _ \/ _]                    |- _                        ] => Check_hyp_is G R
| [                              |- _                        ] => idtac "this isn't something that you can prove using basic definitions"
end.

Tactic Notation "Let's" "prove" ":" constr(Goal) "bsy" "proving" ":"constr(Result):=
definition_unfolder Goal Result.



Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).


Proof.
intros.
help.
Let's prove :( (Image f (A ∩ B) == (Image f A ∩ Image f B))) by proving :((Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) ∧ (Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).
help. 
Let's prove the conjunction :((Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) ∧ (Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).
help.
Let's prove :(Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) by proving :( ∀ x : F, x ∈ Image f (A ∩ B) → x ∈ (Image f A ∩ Image f B)).
help.
Let's fix :y.
help.
Assume H1:(y ∈ Image f (A ∩ B)).
help.
Let's prove :(y ∈ (Image f A ∩ Image f B)) by proving :(y ∈ (λ x : F, x ∈ Image f A ∧ x ∈ Image f B)).
help.
Let's prove the conjunction :(y ∈ (λ x : F, x ∈ Image f A ∧ x ∈ Image f B)).
Show Existentials.
Let's prove :( y ∈ Image f (A ∩ B)) by proving :((Image f (A ∩ B)) y).
help.
Let's prove :(y ∈ Image f A) by proving :((Image f A) y).
help.
Let's prove:(Image f A y) by proving :(∃ x0 : E, x0 ∈ A ∧ y = f x0).
help.
Let's simplify our hypothesis: H1.
help.
Let's show that x fits.
help.
Let's prove the conjunction:(x ∈ A ∧ y = f x).
help.
Let's prove :(x ∈ (A ∩ B)) by proving :((A ∩ B) x).
help.
Let's prove :(In A x) by proving :(A x).
help.
Let's prove :((A ∩ B) x) by proving:(In A x /\ In B x).
Let's simplify our hypothesis :H0.
assumption.
assumption.
help.
Let's prove :(y ∈ Image f (A ∩ B)) by proving :(Image f (A ∩ B) y).
help.
Let's prove :(y ∈ Image f B) by proving :(Image f B y).
Let's prove :(Image f B y) by proving :(exists x, In B x /\ y =f x).
help.
Let's simplify our hypothesis :H1.
Let's show that x fits.
Let's prove the conjunction :(x ∈ B ∧ y = f x).
Let's prove :(x ∈ (A ∩ B)) by proving :((A ∩ B) x).
Let's prove :(In B x) by proving :(B x).
Let's prove :((A ∩ B) x) by proving:(In A x /\ In B x).
Let's simplify our hypothesis :H0.
assumption.
assumption.
Eval unfold Inclusion in ((Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).
Let's prove:((Image f A ∩ Image f B) ⊆ Image f (A ∩ B)) by proving :(∀ x : F, x ∈ (Image f A ∩ Image f B) → x ∈ Image f (A ∩ B)).
Let's fix :y.
Assume H1:(y ∈ (Image f A ∩ Image f B) ). 
Let's prove :(y ∈ Image f (A ∩ B)) by proving :(Image f (A ∩ B) y).
help.
Let's prove :(Image f (A ∩ B) y) by proving :(Image f (λ x : E, x ∈ A ∧ x ∈ B) y).
unfold Image .
Let's prove:(Image f (λ x : E, x ∈ A ∧ x ∈ B) y) by proving :(∃ x : E, x ∈ (λ x0 : E, x0 ∈ A ∧ x0 ∈ B) ∧ y = f x).
help.
Show Existentials.
Let's prove:(y ∈ (Image f A ∩ Image f B)) by proving :( (Image f A ∩ Image f B) y).



Let's show that x fits.
Let's prove the conjunction :(x ∈ (λ x0 : E, x0 ∈ A ∧ x0 ∈ B) ∧ y = f x).
Let's prove the conjunction :(x ∈ (λ x0 : E, x0 ∈ A ∧ x0 ∈ B)).
help.
Let's prove :(H0 : y ∈ Image f A
(* 
unfold Equal.
split.
unfold Inclusion.
intros.
unfold In.
unfold Intersection;unfold Image. split. unfold In. unfold Image in H0. unfold In in H0.
destruct H0.
destruct H0.
 *)
Admitted.




