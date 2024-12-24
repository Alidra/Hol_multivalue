Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2304244 : forall x : int, forall y : int, forall z : int, (int_lt (int_of_num (NUMERAL 0)) z) -> (int_lt (int_mul z x) (int_mul z y)) = (int_lt x y).
