Require Import Utf8.
Require Import Classical.
Require Import Bool.
Require Import CoqVerbose.Concepts.





(*Change the current subgoal*)



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



(* Ltac tester  goal newgoal :=
let Hf := fresh in 
let r := fresh in 
tryif (assert (Hf: goal -> newgoal);[intro r;exact r|idtac];clear Hf) then cut newgoal;[intro r;exact r| idtac] else fail 1 "Wrong anwser, the result you are looking for isn't" newgoal.  

 *)




Ltac tester  goal newgoal :=
let Hf := fresh in 
let r := fresh in 
tryif cut newgoal;[intro r;exact r| idtac] then idtac else fail 1 "Wrong anwser, the result you are looking for isn't" newgoal.  



Ltac verification G R :=



match goal with
  |- In _ _                => tester G R
| |- Inclusion _ _        => unfold Inclusion;tester G R
| |- Union _ _            => unfold Union;tester G R
| |- Intersection _ _     => idtac "Intersection"
| |- Inverse _ _          => idtac "Inverse"
| |- Injective _          => idtac "Injective"
| |- Surjective _         => unfold Surjective;idtac "Surjective"
| |- Equal _ _            => unfold Equal; tester G R
| |- context [Image _ _ ] => unfold Image ;tester G R
| [ H:context[ _ ∈ _ ]           |- _                        ] => check_hyp_is G R

end.

Tactic Notation "We" "need" "to" "prove" "that" ":" constr(Goal) "that" "means" ":"constr(Result):=
verification Goal Result.



Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).


Proof.
intros.
tester ( (Image f (A ∩ B) == (Image f A ∩ Image f B))) ((Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) ∧ (Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).

Admitted.


Theorem reverse_inclusion_verbose :
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.
Proof.
intros E F f Hinj A.
We need to prove that :(Inverse f (Image f A) ⊆ A) that means : (∀ x : E, x ∈ Inverse f (Image f A) → x ∈ A).
intros.
We need to prove that :(x ∈ A) that means: (A x).

We need to prove that :(x ∈ Inverse f (Image f A)) that means :(Inverse f (Image f A) x).


Admitted.




