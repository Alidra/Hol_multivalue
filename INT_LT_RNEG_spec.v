Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2304901 : forall x : int, forall y : int, (int_lt x (int_neg y)) = (int_lt (int_add x y) (int_of_num (NUMERAL 0))).
