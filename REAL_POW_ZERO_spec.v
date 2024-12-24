Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1648695 : forall n : nat, (real_pow (real_of_num (NUMERAL 0)) n) = (@COND real (n = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
