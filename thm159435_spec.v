Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem159435 : forall (m : nat) (n : nat) (h1 : n = (NUMERAL 0)), (Nat.add (Nat.mul n (Nat.div m n)) (Nat.modulo m n)) = m.
