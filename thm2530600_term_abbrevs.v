Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : int) := forall y0 : int, (rem (rem x0 (int_mul x1 y0)) x1) = (rem x0 x1).
Definition term1 (x0 : int) := forall y0 : int, forall y1 : int, (rem (rem x0 (int_mul y0 y1)) y0) = (rem x0 y0).
