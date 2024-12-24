Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2394837 : forall a : int, forall b : int, (~ (b = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem a b).
