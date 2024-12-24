Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7517428 : forall a : nat -> real, forall x : real, forall y : real, forall n : nat, (Peano.le (NUMERAL (BIT1 0)) n) -> (real_sub (@sum nat (dotdot (NUMERAL 0) n) (fun i : nat => real_mul (a i) (real_pow x i))) (@sum nat (dotdot (NUMERAL 0) n) (fun i : nat => real_mul (a i) (real_pow y i)))) = (real_mul (real_sub x y) (@sum nat (dotdot (NUMERAL 0) (Nat.sub n (NUMERAL (BIT1 0)))) (fun j : nat => real_mul (@sum nat (dotdot (NUMERAL 0) (Nat.sub (Nat.sub n j) (NUMERAL (BIT1 0)))) (fun k : nat => real_mul (a (Nat.add j (Nat.add k (NUMERAL (BIT1 0))))) (real_pow y k))) (real_pow x j)))).
