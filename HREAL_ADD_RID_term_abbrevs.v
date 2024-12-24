Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 := hreal_of_num (NUMERAL 0).
Definition term11 := forall y0 : hreal, (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0.
Definition term12 (x0 : hreal) := (fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term10 := forall y0 : hreal, (hreal_add y0 (hreal_of_num (NUMERAL 0))) = y0.
Definition term4 (x0 : hreal) := hreal_add (hreal_of_num (NUMERAL 0)) x0.
Definition term3 (x0 : hreal) := hreal_add x0 (hreal_of_num (NUMERAL 0)).
Definition term7 (x0 : hreal) := @eq hreal (hreal_add (hreal_of_num (NUMERAL 0)) x0).
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_add x0 y0) = (hreal_add y0 x0)) x1.
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add y0 y1) = (hreal_add y1 y0)) x0.
Definition term8 := fun y0 : hreal => (hreal_add y0 (hreal_of_num (NUMERAL 0))) = y0.
Definition term1 (x0 : hreal) := forall y0 : hreal, (hreal_add x0 y0) = (hreal_add y0 x0).
Definition term9 := fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0.
Definition term6 (x0 : hreal) := @eq hreal (hreal_add x0 (hreal_of_num (NUMERAL 0))).
