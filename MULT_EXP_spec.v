Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem88509 : forall p : nat, forall m : nat, forall n : nat, (Nat.pow (Nat.mul m n) p) = (Nat.mul (Nat.pow m p) (Nat.pow n p)).
