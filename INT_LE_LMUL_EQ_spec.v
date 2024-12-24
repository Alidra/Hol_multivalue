Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302576 : forall x : int, forall y : int, forall z : int, (int_lt (int_of_num (NUMERAL 0)) z) -> (int_le (int_mul z x) (int_mul z y)) = (int_le x y).
