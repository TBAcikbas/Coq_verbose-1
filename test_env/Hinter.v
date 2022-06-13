Require Import Utf8.
Ltac Hinter :=
(* order of helps (temporary... )*)
match goal with  
| [ |- ?P -> ?Q] => idtac "When proving A -> B, you need to 'Assume' A in order to prove B"
| [ |- forall x, _ ] => idtac "'Fix' something you shall, when proving a forall"
| [ |- ?Q <->  ?P] => idtac "split your goal into two 'Assume' you shall"
| [ |- _] => idtac "Check your definition, you shall"


end.





Tactic Notation "Master" "yoda" "," "what" "is" "your" "wisdom" "?":= (* To be changed !!!*)
Hinter .


Tactic Notation "Help" "please":=
Hinter.
