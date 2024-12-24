Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1528208 : ((~ ((real_abs (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) -> False) -> (real_abs (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
