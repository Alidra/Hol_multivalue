Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : real) (x1 : real) (x2 : real) := ((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))).