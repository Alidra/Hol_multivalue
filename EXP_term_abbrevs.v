Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term2 := (forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))).
Definition term1 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
