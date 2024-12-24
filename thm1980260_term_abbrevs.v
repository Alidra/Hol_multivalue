Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : real) (x1 : real) := (fun y0 : real => (real_ge y0 x0) = (real_le x0 y0)) x1.
