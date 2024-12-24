Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5393577 : forall m : nat, forall n : nat, @HAS_SIZE nat (dotdot m n) (Nat.sub (Nat.add n (NUMERAL (BIT1 0))) m).
