Require Import Utf8.
Require Import Basics.
Require Import Reals.
Require Import CoqVerbose.src.Concepts.Concepts.
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
| [                              |- ?P                        ] => let result := eval hnf in P in idtac  "Let's prove ("P") by proving (" result ").";folder anchor
end.




Ltac hyp_helper anchor_hyp anchor_goal := 
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
              |H:_ /\ _       |- _  => idtac "By" H "we obtain"  new_instance_first "and" new_instance_second "." ;revert H;hyp_helper anchor_hyp anchor_goal
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




