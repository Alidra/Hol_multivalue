Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem159520 : forall (n : nat) (m : nat), ((~ ((Nat.add (Nat.mul (Nat.div m n) n) (Nat.modulo m n)) = m)) -> False) = ((Nat.add (Nat.mul (Nat.div m n) n) (Nat.modulo m n)) = m).