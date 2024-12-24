Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => (@FCONS a0 x0 y0 (NUMERAL 0)) = x0) x1.
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0) x0.
Definition term2 (a0 : Type') (x0 : a0) := forall y0 : nat -> a0, (@FCONS a0 x0 y0 (NUMERAL 0)) = x0.
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, (@FCONS a0 y0 y1 (NUMERAL 0)) = y0.
