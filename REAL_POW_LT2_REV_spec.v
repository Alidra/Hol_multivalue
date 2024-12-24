Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1651996 : forall n : nat, forall x : real, forall y : real, ((real_le (real_of_num (NUMERAL 0)) y) /\ (real_lt (real_pow x n) (real_pow y n))) -> real_lt x y.
