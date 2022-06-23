Require Import Utf8.
Require Import CoqVerbose.Concepts.


Ltac Hinter :=
match goal with
(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)




(*Hints applied to goals*)
| [                              |- forall x,?P              ] => idtac "Fix x"
| [                              |- ?A -> ?B                   ] => idtac "Assume (H:"A"))"
| [H:?Q                          |- exists x,?P :?Q          ] => idtac "Let's show that (Name of the hypothesis containing the variable) fit" 
| [                              |- context [ ?A <-> ?B ]      ] => idtac "Let's prove the equivalence :(Your current goal) such that we get (Result of unfold Goal))"
| [                              |- context [ ?A == ?B ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- context [ ?A  ⊆ ?B ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- context [ ?A /\ ?B ]       ] => idtac "Let's prove the by proving :(Your current goal) such that we get (First implication) /\ (Second Implication))"
| [                              |- context [ ?A ∩  ?B ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- context [ ?A ∪  ?B ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H:context[?A /\ ?B ]           |- _                        ] => idtac "Let's simplify our hypothesis :(name of your disjunctive hypothesis))"
| [ H:context[exists x,?P]       |- _                        ] => idtac "Let's simplify our hypothesis:(name of the hypothesis)"
| [ H:context[ ?A ∈ ?B ]           |- _                        ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- ?A ∈ ?B                  ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H:context[Image _  _ ]       |- _                        ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H: ?A <->  ?B                  |- _                        ] => idtac "Let's simplify our hypothesis (hypothesis to simplify))"
| [ H: ?A  ⊆ ?B                    |- _                        ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H: ?A ∩ ?B                     |- _                        ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H: ?A ∪ ?B                     |- _                        ] => idtac "By cases on :(Your current goal)"
| [                              |- context [Image _ _]      ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)" 
| [                              |- context [Inverse _ _ ]   ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- context [Right_Inv _ _]  ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- Surjective _             ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [ H:Injective _                |- _                        ] => idtac "Let's apply our hypothesis: (name of your Injective Hypothesis))"
| [ H: ?A \/ ?B                    |- _                        ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal)"
| [                              |- _                        ] => idtac "Error: No Help avaible"
end.