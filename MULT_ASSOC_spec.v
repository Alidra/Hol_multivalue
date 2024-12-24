Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem82357 : forall m : nat, forall n : nat, forall p : nat, (Nat.mul m (Nat.mul n p)) = (Nat.mul (Nat.mul m n) p).
