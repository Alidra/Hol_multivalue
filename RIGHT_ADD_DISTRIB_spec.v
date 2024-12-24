Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem82128 : forall m : nat, forall n : nat, forall p : nat, (Nat.mul (Nat.add m n) p) = (Nat.add (Nat.mul m p) (Nat.mul n p)).
