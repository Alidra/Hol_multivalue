Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309248 : ((real_sgn (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) = ((int_sgn (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))).