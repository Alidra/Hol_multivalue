Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7332366 : forall x : real, forall n : nat, (Peano.le (NUMERAL (BIT1 0)) n) -> (real_sub (real_pow x n) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_sub x (real_of_num (NUMERAL (BIT1 0)))) (@sum nat (dotdot (NUMERAL 0) (Nat.sub n (NUMERAL (BIT1 0)))) (fun i : nat => real_pow x i))).
