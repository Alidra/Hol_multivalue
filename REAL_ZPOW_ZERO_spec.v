Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3174157 : forall n : int, (real_zpow (real_of_num (NUMERAL 0)) n) = (@COND real (n = (int_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
