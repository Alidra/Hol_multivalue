Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7233249 : forall f : nat -> real, forall g : nat -> real, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun k : nat => real_mul (f k) (real_sub (g (Nat.add k (NUMERAL (BIT1 0)))) (g k)))) = (@COND real (Peano.le m n) (real_sub (real_sub (real_mul (f (Nat.add n (NUMERAL (BIT1 0)))) (g (Nat.add n (NUMERAL (BIT1 0))))) (real_mul (f m) (g m))) (@sum nat (dotdot m n) (fun k : nat => real_mul (g (Nat.add k (NUMERAL (BIT1 0)))) (real_sub (f (Nat.add k (NUMERAL (BIT1 0)))) (f k))))) (real_of_num (NUMERAL 0))).
