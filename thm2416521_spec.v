Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416521 : forall (m : int), (int_mul (int_of_num (NUMERAL 0)) m) = (int_of_num (NUMERAL 0)).
