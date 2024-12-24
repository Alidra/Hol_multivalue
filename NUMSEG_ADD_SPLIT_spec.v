Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5459080 : forall m : nat, forall n : nat, forall p : nat, (Peano.le m (Nat.add n (NUMERAL (BIT1 0)))) -> (dotdot m (Nat.add n p)) = (@UNION nat (dotdot m n) (dotdot (Nat.add n (NUMERAL (BIT1 0))) (Nat.add n p))).
