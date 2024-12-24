Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1653544 : forall n : nat, forall x : real, forall y : real, ((~ (n = (NUMERAL 0))) /\ ((real_pow x n) = (real_pow y n))) -> (real_abs x) = (real_abs y).
