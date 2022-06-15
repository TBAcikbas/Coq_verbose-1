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
| [ |- ?P -> ?Q ]     => idtac "When proving A -> B,  'Assume' A in order to prove B"
| [ |- forall x, _ ]  => idtac "When proving a ∀ x,... statement you need to 'Fix x'"
| [ |- ?Q <->  ?P]    => idtac "An '<->' can be prove by simplifying to  Q -> P /\ P -> Q"
| [ |- ?A == ?B  ]    => idtac "An '==' can be prove by unfolding it's definition"
| [ |- ?A /\ ?B ]     => idtac "To prove a conjuction you need to A then B or vise versa"
| [ |- ?A  ⊆ ?B ]     => idtac "An '⊆' can ve proven by proving that if an element belongs to a then it belongs to B aswell"
| [ |- ?A ∈ ?B]       => idtac "An '∈' can be written as A ∈ B or B A (A applied to B)"
| [ |- ?A ∩ ?B]       => idtac "The '∩' can be proven by proving that the element studient is in both sets."
| [ |- (?A ?B) ]      =>  idtac "" (*???*)






(*Hints applied to Hypothesis*)
| [ _:Injective _ |-_ ]    => idtac "An injective hypothesis can be applied to 'f(x) = f(x')'"
| [ _:?A -> ?B |- _]       => idtac "Can be used" 
| [ _:forall x, _ |- _ ]   => idtac "Apply another hypothesis in order to simplify a forall statement" 
| [ _:?Q <->  ?P |- _ ]    => idtac "An '<->' can be simplified "
| [ _:?A /\ ?B |-  _ ]     => idtac "A conjunction hypothesis can be simplified to two hypothesis A and B"
| [ _:?A  ⊆ ?B |- _ ]      => idtac "An   '⊆' can be unfolded in order to get a statement with  assumption"
| [ _:?A ∈ ?B |- _ ]       => idtac "An ∈ can be unfolded if the goal resembles (B A)"
| [ _:?A ∩ ?B |- _ ]       => idtac "Can be unfold with the definition"


| [ |- _] => idtac "Error: No Help avaible"
end.

Tactic Notation "Help" "please":=
Hinter.


Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens) Q (i:F),
    Injective f-> 
    (Im f (A ∩ B)) == ((Im f A) ∩ (Im f B)) -> Q.
Help please.
intros.
unfold Set_eq in H0.
spliter.

unfold Incl in H0.
induction (H0 i).
Abort.



