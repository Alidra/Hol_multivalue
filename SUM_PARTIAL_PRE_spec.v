Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7233425 : forall f : nat -> real, forall g : nat -> real, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun k : nat => real_mul (f k) (real_sub (g k) (g (Nat.sub k (NUMERAL (BIT1 0))))))) = (@COND real (Peano.le m n) (real_sub (real_sub (real_mul (f (Nat.add n (NUMERAL (BIT1 0)))) (g n)) (real_mul (f m) (g (Nat.sub m (NUMERAL (BIT1 0)))))) (@sum nat (dotdot m n) (fun k : nat => real_mul (g k) (real_sub (f (Nat.add k (NUMERAL (BIT1 0)))) (f k))))) (real_of_num (NUMERAL 0))).
