Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301157 : forall x : int, (int_add (int_neg x) x) = (int_of_num (NUMERAL 0)).
