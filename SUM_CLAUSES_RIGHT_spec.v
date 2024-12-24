Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7226365 : forall f : nat -> real, forall m : nat, forall n : nat, ((Peano.lt (NUMERAL 0) n) /\ (Peano.le m n)) -> (@sum nat (dotdot m n) f) = (real_add (@sum nat (dotdot m (Nat.sub n (NUMERAL (BIT1 0)))) f) (f n)).
