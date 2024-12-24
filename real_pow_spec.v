Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1344316 : forall (x : real), ((real_pow x (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall n : nat, (real_pow x (S n)) = (real_mul x (real_pow x n))).
