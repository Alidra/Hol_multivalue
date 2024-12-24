Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416523 : forall (a : int), (int_add (int_of_num (NUMERAL 0)) a) = a.
