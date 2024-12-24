Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1009124 : forall (p : nat) (b : nat) (m : nat) (n : nat) (a : nat), ((Nat.pow m n) = p) -> ((Nat.mul p p) = b) -> ((Nat.mul m b) = a) -> (Nat.pow m (BIT1 n)) = a.
