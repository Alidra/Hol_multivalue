Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7244018 : forall f : nat -> real, forall m : nat, forall n : nat, forall p : nat, ((Peano.le m (Nat.add n (NUMERAL (BIT1 0)))) /\ (Peano.le n p)) -> (real_add (@sum nat (dotdot m n) f) (@sum nat (dotdot (Nat.add n (NUMERAL (BIT1 0))) p) f)) = (@sum nat (dotdot m p) f).
