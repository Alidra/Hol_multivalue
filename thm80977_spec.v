Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem80977 : (forall n : nat, (Nat.mul (NUMERAL 0) n) = (NUMERAL 0)) /\ (forall m : nat, forall n : nat, (Nat.mul (S m) n) = (Nat.add (Nat.mul m n) n)).
