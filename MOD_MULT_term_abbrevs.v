Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul y0 y1) y0) = (NUMERAL 0).