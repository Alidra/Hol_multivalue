Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1321909 : forall m : hreal, (hreal_mul m (hreal_of_num (NUMERAL 0))) = (hreal_of_num (NUMERAL 0)).