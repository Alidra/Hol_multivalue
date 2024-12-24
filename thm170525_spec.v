Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem170525 : (forall m : nat, forall n : nat, (~ (m = (NUMERAL 0))) -> (Nat.div (Nat.mul m n) m) = n) /\ (forall m : nat, forall n : nat, (Nat.modulo (Nat.mul m n) m) = (NUMERAL 0)).
