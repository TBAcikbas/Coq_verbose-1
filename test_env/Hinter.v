Require Import Utf8.
Require Import CoqVerbose.Concepts.
Require Import CoqVerbose.Tactiques.

(* Show Existentials. *)

Ltac Hinter :=
(* Sentences are temporary this files contains hints that will be used in order to help user. 
Messages given during the aplha phase will be changed according to the requirement put forward by the Owner later on*)

match goal with

(*Hints applied to Hypothesis*)
| [ _:Injective _ |-_ ]    => idtac "An injection this is, simplify it you can"
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
| [ |- ?A ?B ]        =>  idtac "Unknow enemy it is, Ask the Master you shall"












| [ |- _] => idtac "Check your definition, you shall"
end.





Tactic Notation "Master" "yoda" "," "what" "is" "your" "wisdom" "?":= (* To be changed !!!*)
Hinter .


Tactic Notation "Help" "please":=
Hinter.


Theorem exercise_inj_inter : ∀  {E F: Type} (f: E -> F) (A B:Ens),
    Injective f -> 
    (Im f (A ∩ B)) == ((Im f A) ∩ (Im f B)).
Proof.

(* Help please. *)

Let's fix values: A,B,C,D,E.

(* Help please. *)

Assume H:(Injective C).
Show Existentials.
Help please.
By definition of Injective applied to the hypothesis :H.




