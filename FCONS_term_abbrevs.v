Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2).
Definition term1 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0.
Definition term2 (a0 : Type') := (forall y0 : a0, forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0) /\ (forall y0 : a0, forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2)).
