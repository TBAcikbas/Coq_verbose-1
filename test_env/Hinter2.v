

Ltac Hinter :=
match goal with
(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)




(*Hints applied to goals*)
| [                              |- forall x,?P              ] => idtac "Fix x)"
| [                              |- _ -> _                   ] => idtac "Assume (H:A))"
| [H:?Q                          |- exists x,?P :?Q          ] => idtac "Let's show that (Name of the hypothesis containing the variable) fit" 
| [                              |- context [ _ <-> _ ]      ] => idtac "Let's prove the equivalence :(Your current goal) such that we get (Result of unfold Goal))"
| [                              |- context [ _ == _ ]       ] => idtac "Let's prove (your current goal) by proving :(Result of unfolded Goal"
| [                              |- context [ _  ⊆ _ ]       ] => idtac "An '⊆' can ve proven by proving that if an element X belongs to A then it belongs to B aswell (exemple: By definition Inclusion applied to : (Your current goal) such that we get (Result of Unfold))"
| [                              |- context [ _ /\ _ ]       ] => idtac "To prove a conjuction you need to A then B or vise versa (exemple :Let's prove the by proving :(Your current goal) such that we get (First implication) and (Second Implication))"
| [                              |- context [ _ ∩  _ ]       ] => idtac "The '∩' can be proven by proving that the element studient is in both sets. (exemple :By definition Intersection applied to : (Your current goal) such that we get (Result of Unfold)))"
| [                              |- context [ _ ∪  _ ]       ] => idtac "The '∪' can be proven by proving that the element belongs to one of the two sets (exemple :By definition Union applied to : (Your current goal) such that we get (Result of Unfold))"
| [ H:context[_ /\ _ ]           |- _                        ] => idtac "A conjunction hypothesis can be simplified to two hypothesis A and B (exemple: Let's simplify our hypothesis :(name of your disjunctive hypothesis))"
| [ H:context[exists x,?P]       |- _                        ] => idtac "You can simplify the hypothesis (exemple :Let's simplify our hypothesis:(name of the hypothesis) such that we get :(Result of the simplification)."
| [ H:context[ _ ∈ _ ]           |- _                        ] => idtac "An ∈ can be unfolded and the hypothesis  will resemble (B A)(exemple : In applied to :(Your current Goal) such that we get (Result of Unfold))"
| [                              |- ?A ∈ ?B                  ] => idtac "An '∈' can be written as A ∈ B or B A (A applied to B) (exemple: By definition In applied to : (Your current goal) such that we get (Result of Unfold)))"
| [ H:context[Image _  _ ]       |- _                        ] =>  idtac "It is possible to rewrite Image by using it's definition (exemple: Prove that:(your hypothesis) such that we get (Result of Unfold))"
| [ H: _ <->  _                  |- _                        ] => idtac "An '<->' can be simplified (exemple: Let's simplify our hypothesis (hypothesis to simplify))"
| [ H: _  ⊆ _                    |- _                        ] => idtac "An   '⊆' can be unfolded to get an implication (exemple : Inclusion applied to :(Your current Goal) such that we get (Result of Unfold))"
| [ H: _ ∩ _                     |- _                        ] =>idtac "An ∩ can be unfolded  in order to help prove thanks to A or B (exemple: Intersection applied to :(your current goal) such that we get (Result of unfold))"
| [ H: _ ∪ _                     |- _                        ] =>idtac "When using a ∪ , you should always prove both cases (exemple:exemple :By cases on :(Your current goal) such that we get (First implication) and (Second Implication))"
| [                              |- context [Image _ _]      ] =>  idtac "Image applied to :(your current goal) such that we get (Result of Unfold)" 
| [                              |- context [Inverse _ _ ]   ] => idtac "It is possible to rewrite Inverse by usint it's definition (exemple: Prove that :(your goal) such that we get (Result of Unfold)"
| [                              |- context [Right_Inv _ _]  ] => idtac "It is possible to rewrite Right_Inv by using it's definition (exemple: Prove that:(your hypothesis) such that we get (Result of Unfold))"
| [                              |- Surjective _             ] =>  idtac "It is possible to rewrite Surjective by using it's definition (exemple: Prove that:(your hypothesis) such that we get (Result of Unfold))"
| [ H:Injective _                |- _                        ] =>  idtac "An injective hypothesis can be applied to 'f(x) = f(x')' (exemple:Let's apply our hypothesis: (name of your Injective Hypothesis))"
| [ H: _ \/ _                    |- _                        ] => idtac "When proving a disjunction which is an hypothesis, you need to prove both cases (exemple : Prove that :(you disjunction) such that we get (Cases)"
| [                              |- _                        ] =>  idtac "Error: No Help avaible"
end.