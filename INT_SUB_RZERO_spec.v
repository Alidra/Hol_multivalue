Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310446 : forall x : int, (int_sub x (int_of_num (NUMERAL 0))) = x.
