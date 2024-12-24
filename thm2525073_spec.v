Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2525073 : (forall n : int, (div (int_of_num (NUMERAL 0)) n) = (int_of_num (NUMERAL 0))) /\ (forall n : int, (rem (int_of_num (NUMERAL 0)) n) = (int_of_num (NUMERAL 0))).
