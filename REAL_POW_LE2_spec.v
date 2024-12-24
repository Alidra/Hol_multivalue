Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1636714 : forall n : nat, forall x : real, forall y : real, ((real_le (real_of_num (NUMERAL 0)) x) /\ (real_le x y)) -> real_le (real_pow x n) (real_pow y n).
