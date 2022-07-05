Require Import Utf8.
Require Import CoqVerbose.src.Concepts.Concepts.

(*Version 1*)

Ltac Hinter :=
match goal with
(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)





(*Hints applied to goals*)
| [                              |- forall x,?P              ] => idtac "Fix x"
| [                              |- _ -> _                   ] => idtac "Assume (H:A))"
| [H:?Q                          |- exists x,?P :?Q          ] => idtac "Let's show that (Name of the hypothesis containing the variable) fit" 
| [                              |- context [ _ <-> _ ]      ] => idtac "Let's prove the equivalence :(Your current goal) such that we get (Result of unfold Goal))"
| [                              |- context [ _ == _ ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- context [ _  ⊆ _ ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- context [ _ /\ _ ]       ] => idtac "Let's prove the by proving :(Your current goal) such that we get (First implication) /\ (Second Implication))"
| [                              |- context [ _ ∩  _ ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- context [ _ ∪  _ ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H:context[_ /\ _ ]           |- _                        ] => idtac "By using our definition in :(name of the hypothesis) such that we get (Result of unfolding Definition)"
| [ H:context[exists x,?P]       |- _                        ] => idtac "Let's simplify our hypothesis:(name of the hypothesis)"
| [ H:context[ _ ∈ _ ]           |- _                        ] => idtac "By using our definition in :(name of the hypothesis) such that we get (Result of unfolding Definition)"
| [                              |- ?A ∈ ?B                  ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H:context[Image _  _ ]       |- _                        ] => idtac "By using our definition in :(name of the hypothesis) such that we get (Result of unfolding Definition)"
| [ H: _ <->  _                  |- _                        ] => idtac "Let's simplify our hypothesis (hypothesis to simplify))"
| [ H: _  ⊆ _                    |- _                        ] => idtac "By using our definition in :(name of the hypothesis) such that we get (Result of unfolding Definition)"
| [ H: _ ∩ _                     |- _                        ] => idtac "By using our definition in :(name of the hypothesis) such that we get (Result of unfolding Definition)"
| [ H: _ ∪ _                     |- _                        ] => idtac "By cases on :(name of your hypothesis)"
| [                              |- context [Image _ _]      ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)" 
| [                              |- context [Inverse _ _ ]   ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- context [Right_Inv _ _]  ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- Surjective _             ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H:Injective _                |- _                        ] => idtac "Let's apply our hypothesis: (name of your Injective Hypothesis))"
| [ H: _ \/ _                    |- _                        ] => idtac "By cases on :(name of your hypothesis)"
| [                              |- _                        ] => idtac "Error: No Help avaible"
end.


(*Version 2 of Hinter 2 *)


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


Ltac hyp_helper_sub_func anchor:=
match goal with
|H: _ |- ?P => hyp_helper anchor P
end.

Tactic Notation "Help" "with" "goal" constr(goal):=
goal_helper goal goal.


Tactic Notation "Help" "with" "hypothesis" constr(hypothesis):=
hyp_helper_sub_func hypothesis.



