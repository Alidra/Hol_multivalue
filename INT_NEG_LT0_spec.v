Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306581 : forall x : int, (int_lt (int_neg x) (int_of_num (NUMERAL 0))) = (int_lt (int_of_num (NUMERAL 0)) x).