Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299582 : forall x : int, forall y : int, (int_gt x y) = (int_ge x (int_add y (int_of_num (NUMERAL (BIT1 0))))).
