oRequire Import Utf8.
Require Import Bool.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.



Example Sym_succ_hyp: forall (f:nat-> nat) x x0, f x =  f x0 -> x = x0.
intros.
By symmetry , using  (f x = f x0) we obtain (f x0 = f x).
Admitted.



Example Sym_fail_hyp: forall (f:nat-> nat) x x0, f x =  f x0 -> x = x0.
intros.
assert_fails (By symmetry , using  (f x = f x0) we obtain (f x0 = f x0)).
Admitted.




Example Sym_succ_goal: forall (f:nat-> nat) x x0, f x =  f x0 -> x = x0.
intros.
By symmetry , using  (x = x0) we obtain (x0 = x).
Admitted.




Example Sym_fail_goal: forall (f:nat-> nat) x x0, f x =  f x0 -> x = x0.
intros.
assert_fails (By symmetry , using  (x = x0) we obtain (x0 = x0)).
Admitted.
