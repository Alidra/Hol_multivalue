Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2436585 : forall x : int, forall y : int, (int_divides x y) -> (int_le (int_abs x) (int_abs y)) \/ (y = (int_of_num (NUMERAL 0))).
