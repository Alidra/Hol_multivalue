Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) := (fun y0 : real => fun y1 : real => real_le y1 y0) x0.
Definition term4 (x0 : real) := forall y0 : real, (real_ge x0 y0) = (real_le y0 x0).
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => (real_ge x0 y0) = (real_le y0 x0)) x1.
Definition term8 (x0 : real) := forall y0 : real, (real_ge y0 x0) = (real_le x0 y0).
Definition term0 := fun y0 : real => fun y1 : real => real_le y1 y0.
Definition term9 := forall y0 : real, forall y1 : real, (real_ge y1 y0) = (real_le y0 y1).
Definition term5 := forall y0 : real, forall y1 : real, (real_ge y0 y1) = (real_le y1 y0).
Definition term2 (x0 : real) := fun y0 : real => real_le y0 x0.
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, (real_ge y0 y1) = (real_le y1 y0)) x0.
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => real_le y0 x0) x1.
