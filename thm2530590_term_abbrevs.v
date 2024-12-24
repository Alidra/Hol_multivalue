Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (rem y0 (int_mul y1 y2)) y2) = (rem y0 y2).
Definition term1 (x0 : int) := forall y0 : int, forall y1 : int, (rem (rem x0 (int_mul y0 y1)) y1) = (rem x0 y1).
Definition term0 (x0 : int) (x1 : int) := forall y0 : int, (rem (rem x1 (int_mul x0 y0)) y0) = (rem x1 y0).
