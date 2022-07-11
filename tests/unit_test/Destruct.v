Require Import Utf8.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.

(*Propositions*)

Ltac destruct_exist'' hypothesis ext first_element second_element :=
match goal with 
|H:hypothesis |-_ =>tryif (destruct H as [ext [first_element second_element]]) then idtac else fail 1 "not existential"
end.




Tactic Notation "By" constr(hypothesis) "we" "obtain" simple_intropattern(ext) "such" "that" "we" "get" simple_intropattern(first_element)  "and" simple_intropattern(second_element):=
destruct_exist'' hypothesis ext first_element second_element .


Theorem reverse_inclusion_verbose_ :
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.

Proof.
intros.
hnf.
intros.
hnf in H0.
By ( ∃ x0 : E, x0 ∈ A ∧ f x = f x0) we obtain  x0 such that we get K1 and K2 .
Admitted.








(* 

(* Expected but "impossible" version *)



Ltac destruct_exist''_2 Hyp P P1 P1_result P2 P2_result  :=
match goal with 
|H:Hyp |-_ => tryif (destruct H as [P [P1 P2]]) then 
          match goal with 
          |H:P1_result, H1:P2_result |- _=> idtac
          |H:_  |-_ => fail 1 "The expected"P1 "and "P2" are not" P1_result "and" P2_result
          end else fail 1 "The expected"P1 "and "P2" are not" P1_result "and" P2_result
end.



Tactic Notation "By" constr(hypothesis) "we" "obtain" simple_intropattern(ext) "such" "that" "we" "get" simple_intropattern(first_element) ":" open_constr(first_element_content) "and" uconstr(second_element) ":" open_constr(second_element_content):=
destruct_exist''_2 hypothesis ext first_element first_element_content second_element second_element_content.


(*Zone test*)
Tactic Notation "Foo" open_constr(bidule) := idtac bidule.

Ltac2 

Theorem reverse_inclusion_verbose_1:
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.

Proof.
intros.
hnf.
intros.
Foo (In x0 A).

hnf in H0.
(By (∃ x0 : E, x0 ∈ A ∧ f x = f x0) we obtain  (x0) such that we get K1:(x0 ∈ A) and (K2) : (f x = f x0)).
Admitted.
 *)


