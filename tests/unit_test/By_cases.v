Require Import Utf8.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.

Example test_by_cases_1 : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
Fix P.
Fix Q.
Assume H: (P \/ Q).
By cases on (P \/ Q).
- Assume HP : P.
  Let's prove the disjunction by proving P.
  assumption.
- Assume HQ: Q.
  Let's prove the disjunction by proving Q.
  assumption.
Qed.

