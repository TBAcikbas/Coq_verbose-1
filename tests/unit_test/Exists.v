Require Import Utf8.
Require Import Classical.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.


Example test_letsprove_5 : exists n:nat, S(n) = 2.
Proof.
Let's prove that 1 fits.
trivial.
Qed.

Example test_letsprove_6 : exists n:nat, S(n) = 2.
Proof.
Let's prove that 1 works ie (2=2).
trivial.
Qed.

 