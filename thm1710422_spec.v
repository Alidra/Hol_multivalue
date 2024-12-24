Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1710422 : (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)).
