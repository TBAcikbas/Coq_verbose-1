Require Import Tactics.
Require Import Utf8.
Require Import Bool.
Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Hinter3.



(*Test zone, Will be erased from Project...*)


Ltac folder  Goal anchor := repeat 
match goal with
|H: _ |- _ => let r := H in 
                                    match anchor with 
                                            | Goal => idtac 
                                            | _ => revert H
                                            end
end.





Ltac goal_helper G anchor :=   let newhyp := fresh in 
match goal with
| [                              |- forall x,?Q              ] => idtac "Let's fix :"x".";intro;goal_helper Q anchor
| [                              |- ?P -> ?Q                  ] => idtac "Assume "newhyp":"P".";intro;goal_helper Q anchor
| [                              |- ?P                        ] => let result := eval hnf in P in idtac "Let's prove :("P") by proving :(" result ").";folder G anchor;idtac anchor
 
end.



Tactic Notation "Help" "with" "goal" ":" constr(goal):=
goal_helper goal goal.


Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
Help with goal :(∀ (A B : Type) (f : A → B), (∃ g : B → A, Right_Inv f g) → Surjective f).

Let's fix : A .
Let's fix : B .
Let's fix : f .
Assume  H : (∃ g : B → A, Right_Inv f g) .
Let's prove :( (Surjective f) ) by proving :( (∀ y : B, ∃ x : A, f x = y) ).


Help with goal :(∀ y : B, ∃ x : A, f x = y).
Let's fix : y .
Let's prove :( (∃ x : A, f x = y) ) by proving :( (∃ x : A, f x = y) ).
