Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300691 : forall x : int, forall y : int, (int_lt (int_abs (int_sub x y)) (int_neg y)) -> int_lt x (int_of_num (NUMERAL 0)).
