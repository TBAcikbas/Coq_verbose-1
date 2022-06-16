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



Ltac Hinter :=
match goal with
(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)




(*Hints applied to goals*)
| [ _:context[?A /\ ?B ]|-  _ ]     => idtac "A conjunction hypothesis can be simplified to two hypothesis A and B (exemple: Let's simplify our hypothesis :(name of your disjunctive hypothesis))"
| [ _:context[Right_Inv _ _]|-_]   => idtac "It is possible to rewrite Right_Inv by using it's definition (exemple: By definition of Image applied to the hypothesis :(your hypothesis) such that we get (Result of Unfold))"
| [ _:context[Image _ _ ]|- _]      => idtac "It is possible to rewrite Image by using it's definition (exemple: By definition of Image applied to the hypothesis :(your hypothesis) such that we get (Result of Unfold))"
| [ _:context[exists x,_]|- _]      => idtac "You can simplify the hypothesis (exemple :Let's simplify our hypothesis:(name of the hypothesis) such that we get :(Result of the simplification)."
| [ _:context[?A ∈ ?B ]|- _ ]       => idtac "An ∈ can be unfolded and the hypothesis  will resemble (B A)(exemple : By definition of In applied to :(Your current Goal) such that we get (Result of Unfold))"
| [ |- ?P -> ?Q ]     => idtac "For implication, you can do (exemple: Assume (H:A))"
| [ |- forall x, _ ]  => idtac "When proving a ∀ x, you can do (exemple: Fix x)"
| [ |- exists x, _ ]  => idtac "When proving a ∃ x, you can use one of your hypothesis to substitute the variable in the current goal (exemple: Let's show that (Name of the hypothesis containing the variable) fit" 
| [ |- context [?Q <->  ?P]]    => idtac "An '<->' can be unfolded by doing (exemple: Let's prove the equivalence :(Your current goal) such that we get (Result of Unfold))"
| [ |- context [?A == ?B ]]    => idtac "An '==' can be unfolded by doing (exemple: 'By definition Equal applied to : (Your current goal) such that we get (Result of Unfold))"
| [ |- context [?A /\ ?B ]]     => idtac "To prove a conjuction you need to A then B or vise versa (exemple :Let's prove the disjunction by proving :(Your current goal) such that we get (First implication) and (Second Implication))"
| [ |- context[?A ∩ ?B] ]      => idtac "The '∩' can be proven by proving that the element studient is in both sets. (exemple :By definition Intersection applied to : (Your current goal) such that we get (Result of Unfold)))"
| [ |- context [ ?A ∪ ?B]]       => idtac "The '∪' can be proven by proving that the element belongs to one of the two sets (exemple :By definition Union applied to : (Your current goal) such that we get (Result of Unfold))"
| [ |- context [?A  ⊆ ?B ]]     => idtac "An '⊆' can ve proven by proving that if an element X belongs to A then it belongs to B aswell (exemple: By definition Inclusion applied to : (Your current goal) such that we get (Result of Unfold))"
| [ |- context [Image _ _]] => idtac "By definition of Image applied to :(your current goal) such that we get (Result of Unfold)" 
| [ |- Surjective (_ )] => idtac "It is possible to rewrite Surjective by using it's definition (exemple: By definition of Image applied to the hypothesis :(your hypothesis) such that we get (Result of Unfold))"
| [ |- ?A ∈ ?B]       => idtac "An '∈' can be written as A ∈ B or B A (A applied to B) (exemple: By definition In applied to : (Your current goal) such that we get (Result of Unfold)))"

| [ _:?Q <->  ?P |- _ ]    => idtac "An '<->' can be simplified (exemple: Let's simplify our hypothesis (hypothesis to simplify))"
| [ _:?A  ⊆ ?B |- _ ]      => idtac "An   '⊆' can be unfolded to get an implication (exemple : By definition of Inclusion applied to :(Your current Goal) such that we get (Result of Unfold))"
| [ _:?A ∩ ?B |- _ ]       => idtac "An ∩ can be unfolded  in order to help prove thanks to A or B (exemple: By definition of Intersection applied to :(your current goal) such that we get (Result of unfold))"
| [ _: ?A ∪ ?B|- _]       => idtac "When using a ∪ , you should always prove both cases (exemple:exemple :By cases on :(Your current goal) such that we get (First implication) and (Second Implication))"
| [_ :Injective _ |-_ ]    => idtac "An injective hypothesis can be applied to 'f(x) = f(x')' (exemple:Let's apply our hypothesis: (name of your Injective Hypothesis))"
| [ _:context[forall x, _] |- _ ]   => idtac "Apply another hypothesis in order to simplify a forall statement (exemple : Let's apply our hypothesis :(Injective hypothesis) applied to the hypothesis (Hypothesis containing a function) such that we get (Result of the application))" 

| [ |- _] => idtac "Error: No Help avaible"
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
help.
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
unfold Image in H0.
help.
Let's simplify our hypothesis :H0.
help.
unfold In in H0.
help.
unfold In in H2.
help.
unfold Image.
help.
unfold In.
help.
split.
help.
exists x0.
help.
split.
help.
assumption.
assumption.
help.
exists x0.
help.
split.
assumption.
assumption.
help.
unfold Intersection.
help.
unfold Inclusion.
help.
intros.
help.
unfold Image in H0.
help.
Let's simplify our hypothesis : H0.
help.
Let's simplify our hypothesis :H1.
help.
unfold In.
help.
unfold In in H0.
help.
unfold In in H1. 
help.
unfold Image. (*by definition of Image applied to :(hypothesis) such that we get (result)*)
help.
exists x0.
help.
split.
help.
unfold In.
help.
split.
assumption.
help.
(*Injective help start*) 
help.
rewrite H2 in H3.
Let's apply our hypothesis :H on the hypothesis :H3.
symmetry in H3.
rewrite H3 in H1.
(*Injective help end*)
assumption.
assumption.
Qed. *)




Theorem right_inverse_surjective : ∀ {A B} (f : A -> B),
  (∃ g, Right_Inv f g) -> Surjective f.

Proof.
help.
intros.
help.
unfold Right_Inv in H.
help.
Let's simplify our hypothesis :H.
help.
unfold Surjective.
help.
intros.
help.
Let's apply our hypothesis :y on the hypothesis :H.

einduction (H y).