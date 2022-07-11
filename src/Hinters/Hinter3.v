Require Import Utf8.
Require Import Bool.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.

(*Test zone, Will be erased from Project...*)


Ltac folder   anchor := repeat 
match goal with
|H: _ |- _ => let r := H in 
                                    match goal with 
                                            |- anchor => idtac
                                            | _ => revert r
                                            end
end.



Ltac Unfolder anchor := repeat
  match goal with 
   |- anchor => idtac
   | _ => intro
  end.



Ltac goal_helper G anchor :=   let newhyp := fresh in 
match goal with
| [ H:?Q                         |- ?Q                        ] => idtac "assumption."
| [ H:?Q -> ?P                   |- ?P                        ] => idtac "Let's apply ("H").";folder anchor
| [                              |- ?P -> ?Q                  ] => idtac "Assume "newhyp":"P".";intro;goal_helper Q anchor
| [                              |- forall x,?Q               ] => idtac "Let's fix "x".";intro;goal_helper Q anchor
| [H:?Q                          |- exists x:?Q,?P            ] => idtac "Let's prove that"H"fits";folder  anchor
| [                              |- ?P \/ ?Q                  ] => idtac "Let's prove the disjucntion ("P"). or Let's prove the disjunction ("Q")."
| [                              |- ?P /\ ?Q                  ] => idtac "Let's prove the conjunction by proving" P "and" Q".";Unfolder anchor
| [                              |- ?P                        ] => let result := eval hnf in P in idtac  "Let's prove ("P") by proving (" result ").";folder anchor
end.




Ltac hyp_helper anchor_hyp anchor_goal  := 
match goal with
|H: ?P |- _ => let r := H in  let current_hyp := P in 
      match current_hyp with
      
      | anchor_hyp =>let new_instance_first := fresh in let new_instance_second := fresh in
           match goal with
              |H:exists x,_   |- _  => idtac "By" H "we obtain"  new_instance_first "and" new_instance_second ".";revert H;Unfolder anchor_goal
              |H:_ /\ _       |- _  => idtac "By" H "we obtain"  new_instance_first "and" new_instance_second ".";revert H;Unfolder anchor_goal
              |H: ?P          |- _  => let result := eval hnf in P in idtac "By definition of "P" we get "result".";revert H;Unfolder anchor_goal
              |H: _ \/ _      |- _  => idtac "By cases on :("H").";Unfolder anchor_goal
           end
      | Type => revert r
      | (?P -> ?Q) => revert r
      
      
      |?P =>let new_instance_first := fresh in let new_instance_second := fresh in
           match goal with
              |H:?Q = ?P, H1: ?Q = ?A|-_ =>  idtac "Let's rewrite"H "as" H1".";Unfolder anchor_goal
              |H:?Q = ?P, H1: ?P ∈ ?A|-_ =>  idtac "Let's rewrite"H "as" H1".";Unfolder anchor_goal
              |H:exists x,_   |- _  => idtac "By" H "we obtain"  new_instance_first "and" new_instance_second ".";revert H;Unfolder anchor_goal
              |H:_ /\ _       |- _  => idtac "By" H "we obtain"  new_instance_first "and" new_instance_second "." ;revert H;Unfolder  anchor_goal
              |H: _ \/ _      |- _  => idtac "By cases on :("H")."
              |H: ?P          |- _  => let result := eval hnf in P in idtac "By definition of "P" we get "result".";revert H;hyp_helper anchor_hyp anchor_goal
           end

      end
end.


Ltac hyp_helper_sub_func anchor:=
match goal with
|H: _ |- ?P => hyp_helper anchor P
end.

Tactic Notation "Help" "with" "goal" constr(goal):=
goal_helper goal goal.


Tactic Notation "Help" "with" "hypothesis" constr(hypothesis):=
hyp_helper_sub_func hypothesis.


Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
Help with goal(∀ (A B : Type) (f : A → B), (∃ g : B → A, Right_Inv f g) → Surjective f).
Let's fix  A .
Let's fix  B .
Let's fix  f .
Assume  H : (∃ g : B → A, Right_Inv f g) .
Let's prove ( (Surjective f) ) by proving ( (∀ y : B, ∃ x : A, f x = y) ).


Help with goal (∀ y : B, ∃ x : A, f x = y).
Let's fix  y .
Let's prove ( (∃ x : A, f x = y) ) by proving ( (∃ x : A, f x = y) ).

Help with hypothesis (∃ g : B → A, Right_Inv f g).
By H we obtain H0 and H1 .
Let's prove that (H0 y) fits.                                                             (*fits trigger the rest of the Hypothesis*)
By H1 it suffices to prove 0.
Qed.



Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).
Proof.
Help with goal(∀ (E F : Type) (f : E → F) (A B : Ens), Injective f → Image f (A ∩ B) == (Image f A ∩ Image f B)).
Let's fix  E .
Let's fix  F .
Let's fix  f .
Let's fix  A .
Let's fix  B .
Assume  H : (Injective f) .
Let's prove ( (Image f (A ∩ B) == (Image f A ∩ Image f B)) ) by proving (
((Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) ∧ (Image f A ∩ Image f B) ⊆ Image f (A ∩ B)) ).

Help with goal(Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)).
Let's prove the conjunction by proving (Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) and
((Image f A ∩ Image f B) ⊆ Image f (A ∩ B)) .




Help with goal (Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)).
Let's prove ( (Image f (A ∩ B) ⊆ (Image f A ∩ Image f B)) ) by proving (
(∀ x : F, x ∈ Image f (A ∩ B) → x ∈ (Image f A ∩ Image f B)) ).

Help with goal (∀ x : F, x ∈ Image f (A ∩ B) → x ∈ (Image f A ∩ Image f B)).
Let's fix  x .

Assume  H0 : (x ∈ Image f (A ∩ B)) .
Let's prove ( (x ∈ (Image f A ∩ Image f B)) ) by proving ( (x ∈ Image f A ∧ x ∈ Image f B) ).

Help with hypothesis (Injective f).
By definition of  (x ∈ Image f (A ∩ B))  we get  (∃ x0 : E, x0 ∈ (A ∩ B) ∧ x = f x0) .
By definition of  F  we get  F .
By definition of  (Injective f)  we get  (∀ x x0 : E, f x = f x0 → x = x0) .

Help with hypothesis (∀ x x0 : E, f x = f x0 → x = x0).
By H0 we obtain H1 and H2 .

Help with hypothesis  (H1 ∈ (A ∩ B) ∧ x = f H1).
By H2 we obtain H0 and H3 .


Help with hypothesis (H1 ∈ (A ∩ B)).
By definition of  (x = f H1)  we get  (x = f H1) .
By definition of  (H1 ∈ (A ∩ B))  we get  (H1 ∈ A ∧ H1 ∈ B) .

Help with hypothesis (x = f H1).
By H0 we obtain H2 and H4 .

Help with goal (x ∈ Image f A ∧ x ∈ Image f B).
Let's prove the conjunction by proving (x ∈ Image f A) and (x ∈ Image f B) .
Help with goal (x ∈ Image f A).
Let's prove ( (x ∈ Image f A) ) by proving ( (∃ x0 : E, x0 ∈ A ∧ x = f x0) ).


Help with goal (∃ x0 : E, x0 ∈ A ∧ x = f x0).
Let's prove that H1 fits.

Help with goal (H1 ∈ A ∧ x = f H1).
Let's prove the conjunction by proving (H1 ∈ A) and (x = f H1) .


Help with goal (A).
assumption.

Help with goal( x= f H1).
assumption.

Help with goal (x ∈ Image f B).
Let's prove ( (x ∈ Image f B) ) by proving ( (∃ x0 : E, x0 ∈ B ∧ x = f x0) ).

Help with hypothesis (∀ x x0 : E, f x = f x0 → x = x0).
By definition of  (H1 ∈ B)  we get  (B H1) .
By definition of  (H1 ∈ A)  we get  (A H1) .


Help with goal (∃ x0 : E, x0 ∈ B ∧ x = f x0).
Let's prove that H1 fits.

Help with goal (H1 ∈ B ∧ x = f H1).
Let's prove the conjunction by proving (H1 ∈ B) and (x = f H1) .

assumption.
assumption.

Help with goal ((Image f A ∩ Image f B) ⊆ Image f (A ∩ B)).
Let's prove ( ((Image f A ∩ Image f B) ⊆ Image f (A ∩ B)) ) by proving (
(∀ x : F, x ∈ (Image f A ∩ Image f B) → x ∈ Image f (A ∩ B)) ).

Help with goal (∀ x : F, x ∈ (Image f A ∩ Image f B) → x ∈ Image f (A ∩ B)).
Let's fix  x .
Assume  H0 : (x ∈ (Image f A ∩ Image f B)) .
Let's prove ( (x ∈ Image f (A ∩ B)) ) by proving ( (∃ x0 : E, x0 ∈ (A ∩ B) ∧ x = f x0) ).

Help with hypothesis  (x ∈ (Image f A ∩ Image f B)).
By definition of  (x ∈ (Image f A ∩ Image f B))  we get  (x ∈ Image f A ∧ x ∈ Image f B) .

Help with hypothesis ( x ∈ Image f A ∧ x ∈ Image f B).
By H0 we obtain H1 and H2 .

Help with hypothesis (x ∈ Image f A).
By definition of  (x ∈ Image f B)  we get  (∃ x0 : E, x0 ∈ B ∧ x = f x0) .
By definition of  (x ∈ Image f A)  we get  (∃ x0 : E, x0 ∈ A ∧ x = f x0) .

Help with hypothesis (∃ x0 : E, x0 ∈ A ∧ x = f x0).

By H2 we obtain H0 and H3 .

Help with hypothesis (∃ x0 : E, x0 ∈ A ∧ x = f x0).
By H1 we obtain H2 and H4 .

Help with hypothesis (H0 ∈ B ∧ x = f H0).
By H4 we obtain H1 and H5 .

Help with hypothesis (H0 ∈ B ∧ x = f H0).
By H3 we obtain H4 and H6 .

Help with goal (∃ x0 : E, x0 ∈ (A ∩ B) ∧ x = f x0).
Let's prove that H2 fits.
Help with goal (H2 ∈ (A ∩ B) ∧ x = f H2).
Let's prove the conjunction by proving (H2 ∈ (A ∩ B)) and (x = f H2) .

Help with goal (H2 ∈ (A ∩ B)).
Let's prove ( (H2 ∈ (A ∩ B)) ) by proving ( (H2 ∈ A ∧ H2 ∈ B) ).

Help with goal (H2 ∈ A ∧ H2 ∈ B).
Let's prove the conjunction by proving (H2 ∈ A) and (H2 ∈ B) .

assumption.



(*experimental part*)
Help with hypothesis (H2 ∈ B).
Let's rewrite H5 as H6 .


(*Application of Injective*) 
apply H in H6.
symmetry in H5.
Help with hypothesis (H0 ∈ B).
Let's rewrite H6 as H4.
assumption.


assumption.

Qed.


