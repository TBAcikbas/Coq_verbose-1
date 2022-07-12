Require Import Utf8.
Require Import CoqVerbose.src.Concepts.Concepts.



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
| [ H:?Q -> ?P                   |- ?P                        ] => idtac "Let's apply :(Name of the hypothesis)";folder anchor
| [                              |- ?P -> ?Q                  ] => idtac "Assume (fresh hypothesis name):(Your hypothesis)";intro;goal_helper Q anchor
| [                              |- forall x,?Q               ] => idtac "Let's fix :name of the hypothesis";intro;goal_helper Q anchor
| [H:?Q                          |- exists x:?Q,?P            ] => idtac "Let's prove that (the hypothesis to prove) fits";folder  anchor
| [                              |- ?P \/ ?Q                  ] => idtac "Let's prove the disjucntion (Left side). or Let's prove the disjunction (Right side)."
| [                              |- ?P                        ] => idtac"Let's prove:(your current goal) by proving:(Result of Unfolded Goal)";folder anchor
end.




Ltac hyp_helper anchor_hyp anchor_goal := 
match goal with
|H: ?P |- _ => let r := H in  let current_hyp := P in 
      match current_hyp with
      
      | anchor_hyp =>let new_instance_first := fresh in let new_instance_second := fresh in
           match goal with
              |H:exists x,_   |- _  => idtac "By (the hypothesis with ∃ ) we obtain (first fresh hypothesis name) and (second fresh hypothesis)";revert H;Unfolder anchor_goal
              |H:_ /\ _       |- _  => idtac "By (the hypothesis with ∃ ) we obtain (first fresh hypothesis name) and (second fresh hypothesis)";revert H;Unfolder anchor_goal
              |H: ?P          |- _  => idtac "By definition of :(Name of the Hypothesis ) we get :(Result of unfolded Hypothesis).";revert H;Unfolder anchor_goal
              |H: _ \/ _      |- _  => idtac "By cases on :(the hypothesis).";Unfolder anchor_goal
           end
      | Type => revert r
      | (?P -> ?Q) => revert r
      
      
      |?P =>let new_instance_first := fresh in let new_instance_second := fresh in
           match goal with
              |H:?Q = ?P, H1: ?Q = ?A |-_ =>  idtac  "Let's rewrite (first hypothesis) as (second hypothesis )";Unfolder anchor_goal
              |H:?Q = ?P, H1: ?P ∈ ?A |-_ =>  idtac  "Let's rewrite (first hypothesis) as (second hypothesis )";Unfolder anchor_goal
              |H:exists x,_           |- _  => idtac "By (the hypothesis with ∃ ) we obtain (first fresh hypothesis name) and (second fresh hypothesis)";revert H;Unfolder anchor_goal
              |H:_ /\ _               |- _  => idtac "By (the hypothesis with ∃ ) we obtain (first fresh hypothesis name) and (second fresh hypothesis)";revert H;hyp_helper anchor_hyp anchor_goal
              |H: _ \/ _              |- _  => idtac "By cases on :(name of your hypothesis)"
              |H: ?P                  |- _  => idtac "Let's prove:(your current goal) by proving:(Result of Unfolded Goal)";revert H;hyp_helper anchor_hyp anchor_goal
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


