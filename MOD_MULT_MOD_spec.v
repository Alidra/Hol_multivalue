Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem231346 : forall m : nat, forall n : nat, forall p : nat, (Nat.modulo m (Nat.mul n p)) = (Nat.add (Nat.mul n (Nat.modulo (Nat.div m n) p)) (Nat.modulo m n)).
