Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem161363 : forall m : nat, forall n : nat, (Nat.add (Nat.mul n (Nat.div m n)) (Nat.modulo m n)) = m.
