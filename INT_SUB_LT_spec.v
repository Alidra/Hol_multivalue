Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310280 : forall x : int, forall y : int, (int_lt (int_of_num (NUMERAL 0)) (int_sub x y)) = (int_lt y x).
