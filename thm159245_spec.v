Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem159245 : forall (m : nat) (n : nat) (h1 : n = (NUMERAL 0)), (Nat.add (Nat.mul (Nat.div m n) n) (Nat.modulo m n)) = m.
