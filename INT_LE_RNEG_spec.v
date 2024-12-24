Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303280 : forall x : int, forall y : int, (int_le x (int_neg y)) = (int_le (int_add x y) (int_of_num (NUMERAL 0))).
