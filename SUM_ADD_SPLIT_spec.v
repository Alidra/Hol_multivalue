Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7222770 : forall f : nat -> real, forall m : nat, forall n : nat, forall p : nat, (Peano.le m (Nat.add n (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot m (Nat.add n p)) f) = (real_add (@sum nat (dotdot m n) f) (@sum nat (dotdot (Nat.add n (NUMERAL (BIT1 0))) (Nat.add n p)) f)).
