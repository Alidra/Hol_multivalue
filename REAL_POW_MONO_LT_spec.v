Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1640304 : forall m : nat, forall n : nat, forall x : real, ((real_lt (real_of_num (NUMERAL (BIT1 0))) x) /\ (Peano.lt m n)) -> real_lt (real_pow x m) (real_pow x n).
