Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299447 : forall x : int, forall y : int, (int_lt x y) = (int_le (int_add x (int_of_num (NUMERAL (BIT1 0)))) y).
