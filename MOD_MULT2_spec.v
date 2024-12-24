Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem185837 : forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.mul m n) (Nat.mul m p)) = (Nat.mul m (Nat.modulo n p)).
