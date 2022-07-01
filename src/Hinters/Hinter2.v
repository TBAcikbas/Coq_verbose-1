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


(*Version 2 of Hinter2*)

Ltac help_goal G :=let newhyp := fresh in let result :=eval hnf in G in
match goal with
| [ H:_ -> ?P                    |- ?P                       ] => idtac "Let's apply our hypothesis :(Name of the hypothesis)"
| [H:?P                          |- ?P                       ] => idtac "assumption"
| [                              |- forall x,?P              ] => idtac "Let's fix :name of the hypothesis"
| [                              |- ?P -> _                  ] => idtac "Assume (fresh hypothesis name):()"
| [                              |- ?P                       ] => idtac "Let's prove:(your current goal) by proving:(Result of Unfolded Goal)"
| [                              |- G                        ] => idtac

end.




Ltac help_hyp hyp_name hyp :=let result := eval hnf in hyp in
match hyp with 

| ?P => idtac "By definition of :(Name of the Hypothesis ) we get :(Result of unfolded Hypothesis)."
| _ \/ _ => idtac "By cases on :(Name of the Hypothesis)."

end.




Tactic Notation "Help" "with" "goal" ":" constr(goal):=
help_goal goal.


Tactic Notation "Help" "with" "Hyp" constr(hyp_name) ":" constr(hyp) :=
help_hyp hyp_name hyp.


