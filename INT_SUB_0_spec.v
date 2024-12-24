Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310063 : forall x : int, forall y : int, ((int_sub x y) = (int_of_num (NUMERAL 0))) = (x = y).
