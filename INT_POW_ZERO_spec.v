Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308946 : forall n : nat, (int_pow (int_of_num (NUMERAL 0)) n) = (@COND int (n = (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))).
