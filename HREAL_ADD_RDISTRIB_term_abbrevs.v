Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_mul x0 x2) (hreal_mul x1 x2).
Definition term7 (x0 : hreal) (x1 : hreal) := hreal_add (hreal_mul x0 x1).
Definition term9 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_mul x1 x0) (hreal_mul x1 x2).
Definition term4 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_mul x0 (hreal_add x1 x2).
Definition term23 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_mul x0 (hreal_add y0 y1)) = (hreal_add (hreal_mul x0 y0) (hreal_mul x0 y1)).
Definition term21 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_mul y2 (hreal_add y0 y1)) = (hreal_add (hreal_mul y2 y0) (hreal_mul y2 y1)).
Definition term20 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_mul (hreal_add y0 y1) y2) = (hreal_add (hreal_mul y0 y2) (hreal_mul y1 y2)).
Definition term17 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_mul y1 (hreal_add x0 y0)) = (hreal_add (hreal_mul y1 x0) (hreal_mul y1 y0)).
Definition term16 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_mul (hreal_add x0 y0) y1) = (hreal_add (hreal_mul x0 y1) (hreal_mul y0 y1)).
Definition term19 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_mul y2 (hreal_add y0 y1)) = (hreal_add (hreal_mul y2 y0) (hreal_mul y2 y1)).
Definition term18 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_mul (hreal_add y0 y1) y2) = (hreal_add (hreal_mul y0 y2) (hreal_mul y1 y2)).
Definition term11 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_mul y0 (hreal_add x0 x1)) = (hreal_add (hreal_mul y0 x0) (hreal_mul y0 x1)).
Definition term15 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_mul y1 (hreal_add x0 y0)) = (hreal_add (hreal_mul y1 x0) (hreal_mul y1 y0)).
Definition term14 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_mul (hreal_add x0 y0) y1) = (hreal_add (hreal_mul x0 y1) (hreal_mul y0 y1)).
Definition term26 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_mul x1 (hreal_add x0 y0)) = (hreal_add (hreal_mul x1 x0) (hreal_mul x1 y0))) x2.
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_mul x0 y0) = (hreal_mul y0 x0)) x1.
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_mul y0 y1) = (hreal_mul y1 y0)) x0.
Definition term24 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_mul x0 (hreal_add y0 y1)) = (hreal_add (hreal_mul x0 y0) (hreal_mul x0 y1))) x1.
Definition term10 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_mul (hreal_add x0 x1) y0) = (hreal_add (hreal_mul x0 y0) (hreal_mul x1 y0)).
Definition term25 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_mul x1 (hreal_add x0 y0)) = (hreal_add (hreal_mul x1 x0) (hreal_mul x1 y0)).
Definition term13 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_mul y0 (hreal_add x0 x1)) = (hreal_add (hreal_mul y0 x0) (hreal_mul y0 x1)).
Definition term6 (x0 : hreal) (x1 : hreal) (x2 : hreal) := @eq hreal (hreal_mul x0 (hreal_add x1 x2)).
Definition term1 (x0 : hreal) := forall y0 : hreal, (hreal_mul x0 y0) = (hreal_mul y0 x0).
Definition term5 (x0 : hreal) (x1 : hreal) (x2 : hreal) := @eq hreal (hreal_mul (hreal_add x0 x1) x2).
Definition term3 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_mul (hreal_add x0 x1) x2.
Definition term12 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_mul (hreal_add x0 x1) y0) = (hreal_add (hreal_mul x0 y0) (hreal_mul x1 y0)).
Definition term22 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_mul y0 (hreal_add y1 y2)) = (hreal_add (hreal_mul y0 y1) (hreal_mul y0 y2))) x0.
