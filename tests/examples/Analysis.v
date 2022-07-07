
Require Import Utf8.
Require Import Reals.
Require Import Basics.
Require Import CoqVerbose.src.Concepts.Concepts.
Require Import CoqVerbose.src.Tactics.Tactics.
Require Import CoqVerbose.src.Hinters.Hinter3.



Open Scope R_scope.



Theorem test :forall (u : nat→ R) (l : R),(∀ n, u n = l) → sequence_tendsto u l.
Proof.
Let's fix u,l.
Assume H0:((∀ n : nat, u n = l)).
Let's prove (sequence_tendsto u l) by proving (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) <= ε).
Let's fix eps.
Assume eps_pos :(eps >0).
Let's prove that (0%nat) fits.
Let's fix N.
Assume N_pos:(N ≥ 0).

By rewriting using the hypothesis ((∀ n : nat, u n = l)) we obtain (Rabs (l - l) <= eps).
Let's simplify.
Let's apply Rlt_le.
It is trivial.
It is trivial.
Qed.






Theorem Leanverbose_ex4  (u:nat -> R) (l:R) (hl : l > 0%R) :  sequence_tendsto u l → ∃ N, ∀ n,n ≥ N -> u n >= (l/2) .
Proof.
Assume H:(sequence_tendsto u l).
By (H (l/2) (eps2_Rgt_R0 l hl)) we obtain N and HN.
Let's prove that N fits.
Let's fix n .
Assume H0 :(n ≥ N).
We have T : (HN n H0) such that we get (Rabs (u n - l) <= l / 2).
By  applying  Rabs_le_le on the hypothesis (Rabs (u n - l) <= l / 2) we obtain ((u n - l) <= l / 2 /\ - (l / 2) <= u n - l).
By T we obtain UN1 and UN2.
We Compute.  (*Tactics for ???? simplification ?? resolve ?? *)
Qed.


Theorem Leanverbose_ex6 ( w v u: nat -> R) (l l':R) (hu : sequence_tendsto u l) (hw : sequence_tendsto w l)
(h : ∀ n, (u n) <= (v n))
(h' : ∀ n, v n <= w n) : sequence_tendsto v l .
Proof.

Let's prove ( (sequence_tendsto v l) ) by proving ( (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (v n - l) <= ε) ).


Let's fix  ε .
Assume  H : (ε > 0) .
Let's prove ( (∃ N : nat, ∀ n : nat, n ≥ N → Rabs (v n - l) <= ε) ) by proving (
(∃ N : nat, ∀ n : nat, n ≥ N → Rabs (v n - l) <= ε) ).


By definition of  (ε > 0)  we get  (0 < ε) .
By definition of  R  we get  R .
By definition of  (∀ n : nat, v n <= w n)  we get  (∀ n : nat, v n <= w n) .
By definition of  (∀ n : nat, u n <= v n)  we get  (∀ n : nat, u n <= v n) .
By definition of  (sequence_tendsto w l)  we get  (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (w n - l) <= ε) .
By definition of  (sequence_tendsto u l)  we get  (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) <= ε) .
We have  HN : (hu ε H) such that we get (∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) <= ε).
We have  HN' : (hw ε H) such that we get (∃ N : nat, ∀ n : nat, n ≥ N → Rabs (w n - l) <= ε). 
By HN we obtain N and HN.
By HN' we obtain N' and HN'.
Let's prove that (max N N') fits.
Let's fix n.
Assume n_pos:(n ≥ Init.Nat.max N N').
By definition of ( n ≥ Init.Nat.max N N') we get (Init.Nat.max N N' ≤ n).
By applying ge_max_iff on the hypothesis (Init.Nat.max N N' ≤ n) we obtain (N ≤ n ∧ N' ≤ n).
By n_pos we obtain hn1 and hn2.
We have  Hn1 : (HN n hn1) such that we get ( Rabs (u n - l) <= ε).
We have  Hn2 : (HN' n hn2) such that we get ( Rabs (w n - l) <= ε).
We have  h : (h n) such that we get (u n <= v n).
We have  h' : (h' n) such that we get (v n <= w n).
By applying Rabs_le_le on the hypothesis (Rabs (u n - l) <= ε) we obtain (u n - l <= ε ∧ - ε <= u n - l).
By applying Rabs_le_le on the hypothesis ( Rabs (w n - l) <= ε) we obtain ( w n - l <= ε ∧ - ε <= w n - l).
By Hn1 we obtain Hn1 and Hnd.
By Hn2 we obtain Hn'1 and Hnd'.
Let's apply Rabs_le.
Let's prove (- ε <= v n - l <= ε) by proving (- ε <= v n - l <= ε).
We Compute.
Qed.





Theorem Leanverbose_ex7 (u:nat -> R) (l:R) : sequence_tendsto u l ↔ ∀ε, ε > 0-> ∃ N, ∀ n, n ≥ N -> Rabs (u n - l) < ε.
Proof.

Let's prove (
(sequence_tendsto u l ↔ (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) < ε))
) by proving (
((sequence_tendsto u l → ∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) < ε)
 ∧ ((∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) < ε) → sequence_tendsto u l)) ).
Let's prove the conjunction by proving ((sequence_tendsto u l → ∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) < ε)) and (((∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) < ε) → sequence_tendsto u l)).
Assume H:(sequence_tendsto u l).
Let's fix eps.
Assume eps_pos:(eps > 0).
hnf in H.
We have  T : (H (eps/2) (eps2_Rgt_R0 eps eps_pos)) such that we get (∃ N : nat,∀ n : nat, n ≥ N → Rabs (u n - l) <= (eps/2)).
By T we obtain N and Th.
Let's prove that N fits.
Let's fix n.
Assume n_pos :(n ≥ N ).
We have  Q : (Th n n_pos) such that we get (Rabs (u n - l) <= eps / 2).
We Compute.
Assume H:((∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) < ε) ).
Let's prove ( (sequence_tendsto u l) ) by proving (
(∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) <= ε) ).
Let's fix eps.
Assume eps_pos:(eps >0).
We have  T :(H eps eps_pos) such that we get (∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - l) < eps).
By T we obtain N and Nh1.
Let's prove that N fits.
Let's fix n.
Assume n_sup_N :(n ≥ N).
We have  Q : (Nh1 n n_sup_N) such that we get (Rabs (u n - l) < eps).
Let's prove (Rabs (u n - l) <= eps) by proving (Rabs (u n - l) < eps ∨ Rabs (u n - l) = eps).
Let's prove the disjunction by proving (Rabs (u n - l) < eps).
assumption.
Qed.




Theorem Leanverbose_ex9 (u: nat -> R) (M : R) (h : is_supremum M u) (h' : increasing u) :
sequence_tendsto u M.
Proof.
Let's prove (sequence_tendsto u M) by proving (∀ ε : R, ε > 0 → ∃ N : nat, ∀ n : nat, n ≥ N → Rabs (u n - M) <= ε).
Let's fix eps.
Assume eps_pos:(eps >0).
By definition of (is_supremum M u) we get ((∀ n : nat, u n <= M) ∧ (∀ ε : R, ε > 0 → ∃ n₀ : nat, u n₀ >= M - ε)).
By definition of (increasing u) we get (∀ n m : nat, n ≤ m → u n <= u m).
By h we obtain inf_M and sup_M_ep.
We have  T : (sup_M_ep eps eps_pos) such that we get ( ∃ n₀ : nat, u n₀ >= M - eps).
By T we obtain n0 and Hn0.
Let's prove that n0 fits.
Let's fix n.
Assume nh0:(n ≥ n0 ).
We have  inf_M' : (inf_M n) such that we get ( u n <= M).
Let's apply Rabs_le.
Let's prove (- eps <= u n - M <= eps) by proving (- eps <= u n - M /\ u n - M <= eps).
We have  h'' : (h' n0 n nh0) such that we get (u n0 <= u n ).
By applying  R_sup_eq_symmetry on the hypothesis ( u n0 >= M - eps) we obtain (M - eps <= u n0 ).
We Compute.
Qed.

