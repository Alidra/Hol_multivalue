Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem85714 : forall m : nat, forall n : nat, ((Nat.mul m n) = (NUMERAL (BIT1 0))) = ((m = (NUMERAL (BIT1 0))) /\ (n = (NUMERAL (BIT1 0)))).
