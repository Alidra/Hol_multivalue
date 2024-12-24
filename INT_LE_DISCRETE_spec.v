Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2332494 : forall x : int, forall y : int, (int_le x y) = (int_lt x (int_add y (int_of_num (NUMERAL (BIT1 0))))).
