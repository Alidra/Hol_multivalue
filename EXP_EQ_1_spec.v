Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem87287 : forall x : nat, forall n : nat, ((Nat.pow x n) = (NUMERAL (BIT1 0))) = ((x = (NUMERAL (BIT1 0))) \/ (n = (NUMERAL 0))).
