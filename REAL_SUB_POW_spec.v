Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7332274 : forall x : real, forall y : real, forall n : nat, (Peano.le (NUMERAL (BIT1 0)) n) -> (real_sub (real_pow x n) (real_pow y n)) = (real_mul (real_sub x y) (@sum nat (dotdot (NUMERAL 0) (Nat.sub n (NUMERAL (BIT1 0)))) (fun i : nat => real_mul (real_pow x i) (real_pow y (Nat.sub (Nat.sub n (NUMERAL (BIT1 0))) i))))).
