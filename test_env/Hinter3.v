Require Import Utf8.
Require Import Basics.
Require Import Reals.
Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Tactics.


(*Version 1 of Hinter3*)

Ltac Hinter stmt :=let newhyp:= fresh in let result := eval hnf in stmt in
match goal with


(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)


| [H:?P                          |- ?P                       ] => idtac "assumption."
| [                              |- forall x,?P              ] => idtac "Let's fix :"x"."
| [                              |- ?P -> _                  ] => idtac "Assume "newhyp":"P"."
| [H:?Q                          |- exists x,?P :?Q          ] => idtac "Let's show that ("H") fits." 
| [ H:context[exists x,?P]       |- _                        ] => idtac "Let's simplify our hypothesis:("H")."
| [ H: _ <->  _                  |- _                        ] => idtac "Let's simplify our hypothesis ("H"))."
| [ H: _ ∪ _                     |- _                        ] => idtac "By cases on :("H")."
| [ H:Injective _                |- _                        ] => idtac "Let's apply our hypothesis: ("H"))."
| [ H: _ \/ _                    |- _                        ] => idtac "By cases on :("H")."
| [ H:_ -> ?P  |- ?P                       ] => idtac "Let's apply our hypothesis :("H")."
| [                              |- ?P                       ] => idtac "Let's prove :("P") by proving :("result")."
| [ H:?P                         |- _                        ] => idtac "By definition of :("H") we get ("result")."
| [                              |- _                        ] => idtac "Error: No Help avaible"
end.



Tactic Notation "help" ":" constr(stmt) :=
Hinter stmt.


(*Version 2 of Hinter3*)

Ltac help_goal G :=let newhyp := fresh in let result :=eval hnf in G in
match goal with
| [H:?P                          |- ?P                       ] => idtac "assumption."
| [                              |- forall x,?P              ] => idtac "Let's fix :"x"."
| [                              |- ?P -> _                  ] => idtac "Assume "newhyp":"P"."
| [                              |- ?P                       ] => idtac "Let's prove:("G") by proving:("result")."
| [                              |- G                        ] => idtac
end.




Ltac help_hyp hyp_name hyp :=let result := eval hnf in hyp in
match hyp with 
| forall x, ?P => idtac "Let's simplify our hypothesis ("hyp_name")."
| ?P => idtac "By definition of :("hyp_name") we get :("result")."
| _ \/ _ => idtac "By cases on :("hyp")."

end.




Tactic Notation "Help" "goal" ":" constr(goal):=
help_goal goal.


Tactic Notation "Help" "Hyp" constr(hyp_name) ":" constr(hyp) :=
help_hyp hyp_name hyp.



Theorem exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).
Proof.
Abort.
(* help :(∀ A B C : Prop, (A ∧ B → C) ↔ (A → B → C)).
Let's fix : A .
Let's fix : B .
Let's fix : C .
help :((A ∧ B → C) ↔ (A → B → C)).
Let's prove :( ((A ∧ B → C) ↔ (A → B → C)) ) by proving :(
(((A ∧ B → C) → A → B → C) ∧ ((A → B → C) → A ∧ B → C))).
help :((A ∧ B → C) → A → B → C).
intros.
help :(A ∧ B → C).
Let's apply our hypothesis :( H ).
help :(A ∧ B).
Let's prove :( (A ∧ B) ) by proving :( (A ∧ B) ).
help :(A).
assumption.
help :B.
assumption.
help:((A → B → C) → A ∧ B → C).
Assume  H : (A → B → C) .
help :(A ∧ B → C).
Assume  H0 : (A ∧ B).
help :((A → B → C)).  (* marche pas pour _ ->_ -> ?P*)
Let's apply our hypothesis :H.
assumption.
assumption.
Qed.
*)



