Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7260931 : forall f : nat -> real, forall m : nat, forall n : nat, forall p : nat, ((Peano.lt (NUMERAL 0) n) /\ ((Peano.le m n) /\ (Peano.le n (Nat.add p (NUMERAL (BIT1 0)))))) -> (real_add (@sum nat (dotdot m (Nat.sub n (NUMERAL (BIT1 0)))) f) (@sum nat (dotdot n p) f)) = (@sum nat (dotdot m p) f).
