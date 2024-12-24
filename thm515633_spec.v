Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem515633 : (forall m : nat, (Nat.pow m 0) = (BIT1 0)) /\ (forall m : nat, forall n : nat, (Nat.pow m (S n)) = (Nat.mul m (Nat.pow m n))).
