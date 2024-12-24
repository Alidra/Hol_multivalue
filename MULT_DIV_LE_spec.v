Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem218679 : forall m : nat, forall n : nat, forall p : nat, Peano.le (Nat.mul m (Nat.div n p)) (Nat.div (Nat.mul m n) p).
