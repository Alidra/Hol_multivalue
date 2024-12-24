Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3169164 : forall z : real, forall i : int, (real_zpow z i) = (@COND real (int_le (int_of_num (NUMERAL 0)) i) (real_pow z (num_of_int i)) (real_inv (real_pow z (num_of_int (int_neg i))))).
