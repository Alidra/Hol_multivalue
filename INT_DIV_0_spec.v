Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2395867 : forall m : int, (div m (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0)).