Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (rem y0 (int_mul y1 y2)) y1) = (rem y0 y1).
