Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem153859 : forall x : nat, forall y : nat, forall n : nat, ((Nat.pow x n) = (Nat.pow y n)) = ((x = y) \/ (n = (NUMERAL 0))).
