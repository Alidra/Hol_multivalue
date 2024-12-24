Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 := fun y0 : nat => ~ ((S y0) = 0).
Definition term2 (x0 : nat) := ~ ((S x0) = 0).
Definition term6 := forall y0 : nat, ~ ((S y0) = 0).
Definition term5 := forall y0 : nat, ~ ((S y0) = (NUMERAL 0)).
Definition term3 := fun y0 : nat => ~ ((S y0) = (NUMERAL 0)).
Definition term1 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term0 (x0 : nat) := @eq nat (S x0).
