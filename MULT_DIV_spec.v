Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3116331 : (forall m : nat, forall n : nat, forall p : nat, (num_divides p m) -> (Nat.div (Nat.mul m n) p) = (Nat.mul (Nat.div m p) n)) /\ (forall m : nat, forall n : nat, forall p : nat, (num_divides p n) -> (Nat.div (Nat.mul m n) p) = (Nat.mul m (Nat.div n p))).
