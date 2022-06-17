Require Import Utf8.
Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Tactiques.



(* Ltac Hinter_yoda := (*Easter egg ??*)
match goal with
(*Hints applied to Hypothesis*)
| [ _:Injective _ |-_ ]    => idtac "An injective statement this is, simplify it you can"
| [ _:forall x, _ |- _ ]   => idtac "Use an other hypothesis you shall, apply it to the forall you will " 
| [ _:?Q <->  ?P |- _ ]    => idtac "Equivalent they are, show the two path they will,simplify the definition you will"
| [ _:?A /\ ?B |-  _ ]     => idtac "show the two path they will,simplify the definition you will"
| [ _:?A  ⊆ ?B |- _ ]      => idtac "Prove that A is included in B you shall"
| [ _:?A ∈ ?B |- _ ]       => idtac "Unfold the marvels of 'In' you shall, show that A is in B you will"
| [ _:?A ∩ ?B |- _ ]       => idtac "Show the might of 'Intersection' you will"



(*Hints applied to goals*)
| [ |- ?P -> ?Q ]     => idtac "When proving A -> B,  'Assume' A in order to prove B you will"
| [ |- forall x, _ ]  => idtac "'Fix' something you shall, when proving a forall"
| [ |- ?Q <->  ?P]    => idtac "split your goal into two 'Assume' you shall"
| [ |- ?A == ?B  ]    => idtac "Equal they are, Prove it you shall"
| [ |- ?A /\ ?B ]     => idtac "A pyramid thisn isn't prove the conjunction you shall"
| [ |- ?A  ⊆ ?B ]     => idtac "Prove that A is included in B you shall"
| [ |- ?A ∈ ?B]       => idtac "Unfold the marvels of 'In' you shall, show that A is in B you will"
| [ |- ?A ∩ ?B]       => idtac "Show the might of 'Intersection' you will"
| [ |- (?A ?B) ]      =>  idtac "Unknow enemy it is, Ask the Master you shall"
| [ |- _] => idtac "Check your definition, you shall"
end.

Tactic Notation "Master" "yoda" "," "what" "is" "your" "wisdom" "?":= (* To be changed !!!*)
Hinter_yoda.

 *)



Ltac Hinter_2 :=
match goal with
(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)




(*Hints applied to goals*)
| [                              |- _ -> _                   ] => intro
| [                              |- forall x,?P              ] => Let's fix : ?P
| [H:?Q                          |- exists x,?P :?Q              ] => (*Unknown ??*) exists H
| [H:exists x,?P                 |- _                        ] => simpl_hyp H
| [                              |- context [ _ <-> _ ]      ] => split
| [                              |- context [ _ == _ ]       ] => unfold Equal
| [                              |- context [ _ /\ _ ]       ] => split
| [                              |- context [ _ ∩  _ ]       ] => unfold Intersection
| [                              |- context [ _ ∪  _ ]       ] => unfold Union
| [                              |- context [ _  ⊆ _ ]       ] => unfold Inclusion
| [ H:context[_ /\ _ ]           |- _                        ] => simpl_hyp H 
| [ H:context[exists x,?P], T: _ |- _                        ] => (*Unknown*) idtac "welp"
| [ H:context[ _ ∈ _ ]           |- _                        ] => unfold In in H
| [                              |- ?A ∈ ?B                  ] => unfold In
| [ H: _ <->  _                  |- _                        ] => simpl_hyp 
| [ H: _  ⊆ _                    |- _                        ] => unfold Inclusion in
| [ H: _ ∩ _                     |- _                        ] => unfold Intersection in H
| [ H: _ ∪ _                     |- _                        ] => unfold Union in H
| [ H:context [?P -> ?Q],   T: _ |- _                        ] => induction (H T)
| [                              |- context [Image _ _]      ] => unfold Image
| [                              |- context [Inverse _ _ ]   ] => unfold Inverse
| [                              |- context [Right_Inv _ _]  ] => unfold Right_Inv
| [ H:context[Image _  _ ]       |- _                        ] => unfold Image in H
| [                              |- Surjective _             ] => unfold Surjective
| [ H:Injective _                |- _                        ] => unfold Injective in H
| [                              |- ?P _ = ?P _              ] => f_equal
| [ H:Injective ?P ,Q:?P _ = ?P _  |-_                         ] => apply H in Q
| [                              |- _                        ] => tryif (assumption) then idtac else idtac "Error: No Help avaible"
end.

Tactic Notation "Help" "Please":=
Hinter_2.

Tactic Notation "help":=
Hinter_2.


Tactic Notation "Help":=
Hinter_2.



Theorem direct_Inclusion_verbose:
  forall {E F: Type} (f: E → F),
     ∀ A, A ⊆ Inverse f (Image f A).

Proof.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
Qed. 


Theorem reverse_inclusion_verbose :
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.
Proof.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
apply H in H1.
symmetry in H1.
rewrite H1 in H0.
help.
Qed.

Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).
Proof.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
help.
rewrite H2 in H3.
apply H in H3.
symmetry in H3.
rewrite H3 in H1.
help.
help.
help.
help.
help.
help.
Qed.



Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
help.
help.
help.
help.
help.
help.
help.
exists (x y).
help.
trivial.
Qed.









