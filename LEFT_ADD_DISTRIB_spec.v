Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem82055 : forall m : nat, forall n : nat, forall p : nat, (Nat.mul m (Nat.add n p)) = (Nat.add (Nat.mul m n) (Nat.mul m p)).
