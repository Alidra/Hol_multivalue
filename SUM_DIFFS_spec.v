Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7235163 : forall (f : nat -> real), forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun k : nat => real_sub (f k) (f (Nat.add k (NUMERAL (BIT1 0)))))) = (@COND real (Peano.le m n) (real_sub (f m) (f (Nat.add n (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
