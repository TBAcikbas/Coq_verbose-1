Require Import Utf8.
Require Import Basics.
Require Import Reals.
Require Import CoqVerbose.src.Tactics.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


(*Version 1 of Hinter3*)

Ltac Hinter stmt :=let newhyp:= fresh in let result := eval hnf in stmt in
match goal with


(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)


| [H:?P                          |- ?P                       ] => idtac "assumption."
| [                              |- forall x,?P              ] => idtac "Let's fix :"x"."
| [                              |- ?P -> _                  ] => idtac "Assume "newhyp":"P"."
| [H:?Q                          |- exists x,?P :?Q          ] => idtac "Let's show that ("H") fits." 
| [ H:context[exists x,?P]       |- _                        ] => idtac "Let's prove ("H") by proving ("H")"
| [ H: _ <->  _                  |- _                        ] => idtac "Let's prove ("H") by proving ("H")"
| [ H: _ ∪ _                     |- _                        ] => idtac "By cases on :("H")."
| [ H:Injective _                |- _                        ] => idtac "Let's apply our hypothesis: ("H"))."
| [ H: _ \/ _                    |- _                        ] => idtac "By cases on :("H")."
| [ H:_ -> ?P  |- ?P                       ] => idtac "Let's apply our hypothesis :("H")."
| [                              |- ?P                       ] => idtac "Let's prove :("P") by proving :("result")."
| [ H:?P                         |- _                        ] => idtac "By definition of :("H") we get ("result")."
| [                              |- _                        ] => idtac "Error: No Help avaible with"
end.



Tactic Notation "help" ":" constr(stmt) :=
Hinter stmt.


(*Version 2 of Hinter3*)

Ltac help_goal G :=let newhyp := fresh in let result :=eval hnf in G in
match goal with

| [ H:?P                         |- ?P                       ] => idtac "assumption."
| [                              |- ?P -> _                  ] => idtac "Assume "newhyp":"P"."
| [                              |- forall x,?P              ] => idtac "Let's fix :"x"."
| [H:?Q                          |- exists x,?P :?Q          ] => idtac "Let's show that ("H") fits."

| [                              |- G                        ] => idtac
end.




Ltac help_hyp hyp_name hyp :=let result := eval hnf in hyp in
match hyp with 

| ?P => match goal with
             
              |H :?P   |- _  =>  idtac "By definition of :("hyp_name") we get :("result")."
        end

| _ \/ _ => idtac "By cases on :("hyp")."

end.




Tactic Notation "Help" "with" "Goal" ":" constr(goal):=
help_goal goal.


Tactic Notation "Help" "with" "Hyp" constr(hyp_name) ":" constr(hyp) :=
help_hyp hyp_name hyp.


(*Simple exemple demonstrating both help*)
Theorem exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).
Proof.
Abort.
(* 
help :(∀ A B C : Prop, (A ∧ B → C) ↔ (A → B → C)).
Show Existentials.
Let's fix : A .
Show Existentials.
Let's fix : B .
Show Existentials.
Let's fix : C .
help :((A ∧ B → C) ↔ (A → B → C)).
Let's prove :( ((A ∧ B → C) ↔ (A → B → C)) ) by proving :( (((A ∧ B → C) → A → B → C) ∧ ((A → B → C) → A ∧ B → C)) ).
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
help :((A → B → C)).  (* Doesn't work with _ ->_ -> ?P*)
Let's apply our hypothesis :H.
assumption.
assumption. *)



Theorem exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).
Proof.
Abort.
(* Help with goal :(∀ A B C : Prop, (A ∧ B → C) ↔ (A → B → C)). (*Let's fix : A .*)
Let's fix : A .
intros B C.
Help with goal :((A ∧ B → C) ↔ (A → B → C)).
Let's prove:( ((A ∧ B → C) ↔ (A → B → C)) ) by proving:(
(((A ∧ B → C) → A → B → C) ∧ ((A → B → C) → A ∧ B → C)) ).
Help with goal :((A ∧ B → C) → A → B → C).
Assume  H : (A ∧ B → C) .
Help with goal :(A → B → C).
Assume  H0 : A .
Assume  H1 : B .
Help with goal :(C).
Let's apply our hypothesis :( H ).
Help with goal:(A ∧ B).
Let's prove:( (A ∧ B) ) by proving:( (A ∧ B) ).
Help with goal :(A).
assumption.
assumption.
Help with goal :((A → B → C) → A ∧ B → C).
Assume  H : (A → B → C) .
Help with goal: (A ∧ B → C).
Assume  H0 : (A ∧ B) .
Help with Hyp H0 : (A ∧ B).
By definition of :( H0 ) we get :( (A ∧ B) ).
Let's apply our hypothesis :H.
Help with goal :(A). (* Doesn't work with _ ->_ -> ?P*) 
assumption.
assumption.
Qed. *)


(*Complexe exemple with help*)

Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
Abort.
(* intros.
destruct H.
Help with Hyp H : (Right_Inv f x). (*anwser : Let's fix : A .*)
By definition of :( H ) we get :( (∀ x0 : B, f (x x0) = x0) ).
Help with goal :(Surjective f).

Let's prove:( (Surjective f) ) by proving:( (∀ y : B, ∃ x : A, f x = y) ).

Help with goal :(∀ y : B, ∃ x0 : A, f x0 = y).
Let's fix : y .
Help with goal :(∃ x0 : A, f x0 = y).
Let's show that ( x y ) fits.
Let's apply our hypothesis :H.
Qed. *)







