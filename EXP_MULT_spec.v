Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem88950 : forall m : nat, forall n : nat, forall p : nat, (Nat.pow m (Nat.mul n p)) = (Nat.pow (Nat.pow m n) p).
