Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301545 : forall x : int, forall y : int, ((int_add x y) = x) = (y = (int_of_num (NUMERAL 0))).
