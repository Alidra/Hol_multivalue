Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318057 : forall (x : int), ((int_pow x (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (forall n : nat, (int_pow x (S n)) = (int_mul x (int_pow x n))).
