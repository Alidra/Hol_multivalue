Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303802 : forall x : int, forall y : int, (int_lt y (int_add x y)) = (int_lt (int_of_num (NUMERAL 0)) x).