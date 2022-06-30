Require Import Utf8.
Require Import Bool.
Require Import CoqVerbose.src.Tactics.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.
Require Import CoqVerbose.src.Hinters.Hinter3.



(*Test zone, Will be erased from Project...*)


Ltac folder   anchor := repeat 
match goal with
|H: _ |- _ => let r := H in 
                                    match goal with 
                                            |- anchor => idtac
                                            | _ => revert r
                                            end
end.



Ltac unfolder  := repeat
  match goal with 
|H: _      |-_ => intro
end.






Ltac goal_helper G anchor :=   let newhyp := fresh in 
match goal with
| [ H:_ -> ?P                    |- ?P                       ] => idtac "Let's apply our hypothesis :("H").";intro;goal_helper P anchor
| [                              |- forall x,?Q              ] => idtac "Let's fix :"x".";intro;goal_helper Q anchor
| [                              |- ?P -> ?Q                  ] => idtac "Assume "newhyp":"P".";intro;goal_helper Q anchor
| [                              |- ?P                        ] => let result := eval hnf in P in idtac "Let's prove :("P") by proving :(" result ").";folder anchor
end.    



Ltac hyp_helper anchor := 
 match goal with

|H :?P          |- _  => let result := eval hnf in P in idtac "By definition of :"H" we get :"result".";folder anchor
|H: _ \/ _      |- _  => idtac "By cases on :("H")."

end.




Tactic Notation "Help" "with" "goal" ":" constr(goal):=
goal_helper goal goal.




