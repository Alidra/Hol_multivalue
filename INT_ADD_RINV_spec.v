Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301245 : forall x : int, (int_add x (int_neg x)) = (int_of_num (NUMERAL 0)).
