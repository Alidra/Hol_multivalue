Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt y0 x0) = (real_lt x0 y0)) x1.
Definition term1 (x0 : real) := forall y0 : real, (real_gt y0 x0) = (real_lt x0 y0).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_gt y1 y0) = (real_lt y0 y1)) x0.
