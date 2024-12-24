Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1637789 : forall m : nat, forall n : nat, forall x : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) x) /\ (Peano.le m n)) -> real_le (real_pow x m) (real_pow x n).
