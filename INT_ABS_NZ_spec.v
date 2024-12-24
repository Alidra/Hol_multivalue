Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300505 : forall x : int, (~ (x = (int_of_num (NUMERAL 0)))) = (int_lt (int_of_num (NUMERAL 0)) (int_abs x)).
