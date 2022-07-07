Require Import Utf8.
Require Import CoqVerbose.src.Concepts.Concepts.







Ltac Hinter_2 :=
repeat
match goal with
(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)

| [                              |- _ -> _                   ] => intro
| [                              |- forall x,?P              ] => intro P
| [H:?Q                          |- exists x,?P :?Q          ] => exists H
| [H:exists x,?P                 |- _                        ] => induction H
| [                              |- context [ _ <-> _ ]      ] => split
| [                              |- context [ _ == _ ]       ] => unfold Equal
| [                              |- context [ _ /\ _ ]       ] => split
| [                              |- context [ _ ∩  _ ]       ] => unfold Intersection
| [                              |- context [ _ ∪  _ ]       ] => unfold Union
| [                              |- context [ _  ⊆ _ ]       ] => unfold Inclusion
| [ H:context[_ /\ _ ]           |- _                        ] => induction H 
| [                              |- ?A ∈ ?B                  ] => unfold In
| [ H: _ <->  _                  |- _                        ] => split
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
| [ H:Injective ?P,H2: ?P _ = ?P _  |- _                     ] => tryif (apply H in H2) then idtac else fail 0 "Not an Injection"
| [                              |- _                        ] => tryif (assumption) then idtac else fail 0 "Error: No Help avaible"

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
Qed.
 

Theorem reverse_inclusion_verbose :
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.
Proof.
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
rewrite H2 in H3.
apply H in H3.
symmetry in H3.
rewrite H3 in H0.
help.
Qed.



Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
help.
exists (x y).
trivial.
Qed.









