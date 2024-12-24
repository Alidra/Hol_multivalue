Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308267 : forall n : nat, forall x : int, forall y : int, ((int_le (int_of_num (NUMERAL 0)) x) /\ (int_le x y)) -> int_le (int_pow x n) (int_pow y n).
