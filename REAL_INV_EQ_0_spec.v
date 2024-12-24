Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1588944 : forall x : real, ((real_inv x) = (real_of_num (NUMERAL 0))) = (x = (real_of_num (NUMERAL 0))).
