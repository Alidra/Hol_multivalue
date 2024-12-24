Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem184094 : forall m : nat, forall n : nat, forall p : nat, ((~ (n = (NUMERAL 0))) /\ (Peano.le n p)) -> (Nat.modulo (Nat.modulo m n) p) = (Nat.modulo m n).
