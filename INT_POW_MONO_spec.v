Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308685 : forall m : nat, forall n : nat, forall x : int, ((int_le (int_of_num (NUMERAL (BIT1 0))) x) /\ (Peano.le m n)) -> int_le (int_pow x m) (int_pow x n).
