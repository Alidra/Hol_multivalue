Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))).
Definition term0 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term1 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
