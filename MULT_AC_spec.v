Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem83517 : forall (n : nat) (m : nat) (p : nat), ((Nat.mul m n) = (Nat.mul n m)) /\ (((Nat.mul (Nat.mul m n) p) = (Nat.mul m (Nat.mul n p))) /\ ((Nat.mul m (Nat.mul n p)) = (Nat.mul n (Nat.mul m p)))).
