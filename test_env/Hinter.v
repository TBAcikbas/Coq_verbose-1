Require Import Utf8.
Require Import CoqVerbose.Concepts.


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





Ltac Hinter :=
match goal with
(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)




(*Hints applied to goals*)
| [                              |- forall x,?P              ] => idtac "When proving a ∀ x, you need to fix x."
| [                              |- _ -> _                   ] => idtac "For implication, you need to assume A in order to prove B."
| [H:?Q                          |- exists x,?P :?Q          ] => idtac "When proving a ∃ x, you can use one of your hypothesis to substitute the variable in the current goal." 
| [                              |- context [ _ <-> _ ]      ] => idtac "An '<->' can be unfolded."
| [                              |- context [ _ == _ ]       ] => idtac "An '==' can be unfolded."
| [                              |- context [ _  ⊆ _ ]       ] => idtac "An '⊆' can ve proven by proving that if an element X belongs to A then it belongs to B aswell."
| [                              |- context [ _ /\ _ ]       ] => idtac "To prove a conjuction you need to A then B or vise versa."
| [                              |- context [ _ ∩  _ ]       ] => idtac "The '∩' can be proven by proving that the element studient is in both sets."
| [                              |- context [ _ ∪  _ ]       ] => idtac "The '∪' can be proven by proving that the element belongs to one of the two sets."
| [ H:context[_ /\ _ ]           |- _                        ] => idtac "A conjunction hypothesis can be simplified to two hypothesis A and B."
| [ H:context[exists x,?P]       |- _                        ] => idtac "You can simplify the hypothesis."
| [ H:context[ _ ∈ _ ]           |- _                        ] => idtac "An ∈ can be unfolded in the hypothesis  will resemble (B A)."
| [                              |- ?A ∈ ?B                  ] => idtac "An '∈' can be written as A ∈ B or B A (A applied to B)."
| [                              |- context [Image _ _]      ] =>  idtac "It is possible to rewrite Image(goal) by using it's definition." 
| [                              |- context [Inverse _ _ ]   ] => idtac "It is possible to rewrite Inverse by using it's definition."
| [                              |- context [Right_Inv _ _]  ] => idtac "It is possible to rewrite Right_Inv by using it's definition."
| [ H:context[Image _  _ ]       |- _                        ] =>  idtac "It is possible to rewrite Image(hypothesis) by using it's definition."
| [ H: _ <->  _                  |- _                        ] => idtac "An '<->' can be simplified."
| [ H: _  ⊆ _                    |- _                        ] => idtac "An  '⊆' can be unfolded to get an implication."
| [ H: _ ∩ _                     |- _                        ] =>idtac "An ∩ can be unfolded  in order to help prove thanks to A or B."
| [ H: _ ∪ _                     |- _                        ] =>idtac "When using a ∪ , you should always prove both cases."
| [                              |- Surjective _             ] =>  idtac "It is possible to rewrite Surjective by using it's definition."
| [ H:Injective _                |- _                        ] =>  idtac "An injective hypothesis can be applied to 'f(x) = f(x')'."
| [ H: _ \/ _                    |- _                        ] => idtac "When proving a disjunction which is an hypothesis, you need to prove both cases."
| [                              |- _                        ] =>  idtac "Error: No Help avaible"
end.

Tactic Notation "Help" "Please":=
Hinter.

Tactic Notation "help":=
Hinter.


Tactic Notation "Help":=
Hinter.


(* Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Image f (A ∩ B)) == ((Image f A) ∩ (Image f B)).
Proof.
Help Please.
Let's fix values: A,B,C,D,E.
help. (*error*)
Assume H:(Injective C).
Help Please.
unfold Equal.
Help.
split.
help.
unfold Intersection.
help.
unfold Inclusion.
help.
intros.
help.
split.
help.
simpl_hyp H0.
help.
unfold In in H0.
unfold In in H2.
help.
unfold In.
help.
unfold Image.
help.
exists x0.
help.
split.
help.
unfold In.
assumption.
assumption.
help.
simpl_hyp H0.
help.
unfold In.
help.
unfold In in H0.
unfold In in H2.
help.
unfold Image.
help.
exists x0.
help.
split.
help.
unfold In.
assumption.
assumption.
help.
unfold Intersection.
help.
unfold Inclusion.
help.
intros.
help.
unfold Image.
help.
unfold In.
help.
unfold In in H0.
help.
unfold Image in H0.
simpl_hyp H0.
help.
exists x0.
help.
split.
split.
help.
simpl_hyp H1.
help.
unfold In in H0.
help.
unfold In in H1.
assumption.
help.
simpl_hyp H1.
unfold In in H0.
unfold In in H1.
(*Injective help start*) 
help.
rewrite H2 in H3.
Let's apply our hypothesis :H on the hypothesis :H3.
symmetry in H3.
rewrite H3 in H1.
(*Injective help end*)
assumption.
assumption.
Qed.

 *)
(* 

Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.
Proof.
help.
Let's fix values : A,B,f.
help.
Assume H0 :(∃ g : B → A, Right_Inv f g).
help.
Let's simplify our hypothesis :H0.
help.
unfold Surjective.
help.
intros.
help.
exists (x y).
Let's apply our hypothesis :H.
Qed.
 


Theorem reverse_inclusion_verbose :
  ∀ {E F: Type} (f: E -> F),
    Injective f -> 
      ∀ A, (Inverse f (Image f A)) ⊆ A.

Proof.
help.
intros.
help.
unfold Inclusion.
help.
intros.
help.
unfold In in H0.
help.
unfold In.
help.
unfold Image in H0.
help.
Let's simplify our hypothesis :H0.
help.
unfold In in H0.
help.
apply H in H1.
symmetry in H1.
rewrite H1 in H0.
assumption.
Qed.



Theorem exercice_27 : 
  forall A B C: Prop,  
    (((A /\ B) -> C) <-> ( A -> (B -> C))).
Proof.
help.
intros.
help.
split.
help.
intros.
help.
apply H.
help.
split.
assumption.
assumption.
help.
intros.
help.
apply H.
help.
apply H0.
apply H0.
Qed.  *)
