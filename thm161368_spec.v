Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem161368 : forall (m : nat), forall n : nat, (Nat.add (Nat.mul (Nat.div m n) n) (Nat.modulo m n)) = m.