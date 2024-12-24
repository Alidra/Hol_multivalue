Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem137108 : forall m : nat, forall n : nat, forall p : nat, (Nat.mul (Nat.sub m n) p) = (Nat.sub (Nat.mul m p) (Nat.mul n p)).
