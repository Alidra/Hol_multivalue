Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302053 : forall x : int, forall y : int, ((int_le (int_of_num (NUMERAL 0)) x) /\ (int_lt (int_of_num (NUMERAL 0)) y)) -> int_lt (int_of_num (NUMERAL 0)) (int_add x y).