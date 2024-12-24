Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308008 : forall n : nat, forall x : int, forall y : int, ((~ (n = (NUMERAL 0))) /\ ((int_pow x n) = (int_pow y n))) -> (int_abs x) = (int_abs y).
