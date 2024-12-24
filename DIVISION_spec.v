Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem157261 : forall m : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> (m = (Nat.add (Nat.mul (Nat.div m n) n) (Nat.modulo m n))) /\ (Peano.lt (Nat.modulo m n) n).
