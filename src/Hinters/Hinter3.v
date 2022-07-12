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
| [H:?Q                          |- exists x:?Q,?P            ] => idtac "Let's prove that"H"fits .";folder  anchor
| [                              |- ?P \/ ?Q                  ] => idtac "Let's prove the disjucntion ("P"). or Let's prove the disjunction ("Q")."
| [                              |- ?P /\ ?Q                  ] => idtac "Let's prove (" P "/\" Q  ") by proving" P "and" Q".";Unfolder anchor
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
      | Type => Unfolder anchor_goal
      | (?P -> ?Q) => Unfolder anchor_goal
      | Ens => Unfolder anchor_goal
      
      
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

Ltac Helper :=
match goal with
    
|H:_ |- ?P =>hyp_helper H P;goal_helper P P
|    |- ?P => goal_helper P P
end.

Tactic Notation "Helper":=
Helper.




