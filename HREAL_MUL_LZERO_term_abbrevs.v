Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 := hreal_of_num (NUMERAL 0).
Definition term8 := forall y0 : hreal, (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0.
Definition term34 (x0 : hreal) := imp ((hreal_add (hreal_of_num (NUMERAL 0)) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0)) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) x0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0))).
Definition term12 := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_mul (hreal_add y0 y1) y2) = (hreal_add (hreal_mul y0 y2) (hreal_mul y1 y2))) (hreal_of_num (NUMERAL 0)).
Definition term9 := forall y0 : hreal, y0 = (hreal_add (hreal_of_num (NUMERAL 0)) y0).
Definition term24 (x0 : hreal) := hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0.
Definition term37 (x0 : hreal) := ((hreal_of_num (NUMERAL 0)) = (hreal_mul (hreal_of_num (NUMERAL 0)) x0)) -> (hreal_mul (hreal_of_num (NUMERAL 0)) x0) = (hreal_of_num (NUMERAL 0)).
Definition term11 (x0 : hreal) := (fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term16 := hreal_of_num (NUMERAL (BIT1 0)).
Definition term4 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => ((hreal_add x0 y0) = (hreal_add x1 y0)) = (x0 = x1)) x2.
Definition term21 := hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL (BIT1 0))).
Definition term26 (x0 : hreal) := @eq hreal (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0).
Definition term15 := (fun y0 : hreal => forall y1 : hreal, (hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) y0) y1) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) y1) (hreal_mul y0 y1))) (hreal_of_num (NUMERAL (BIT1 0))).
Definition term19 (x0 : hreal) := hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL (BIT1 0)))) x0.
Definition term5 (x0 : hreal) := hreal_add (hreal_of_num (NUMERAL 0)) x0.
Definition term31 (x0 : hreal) := ((hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) x0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0))) -> (hreal_mul (hreal_of_num (NUMERAL 0)) x0) = (hreal_of_num (NUMERAL 0)).
Definition term30 (x0 : hreal) := ((hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL (BIT1 0)))) x0) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) x0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0))) -> (hreal_mul (hreal_of_num (NUMERAL 0)) x0) = (hreal_of_num (NUMERAL 0)).
Definition term38 := forall y0 : hreal, (hreal_mul (hreal_of_num (NUMERAL 0)) y0) = (hreal_of_num (NUMERAL 0)).
Definition term35 (x0 : hreal) := ((hreal_add (hreal_of_num (NUMERAL 0)) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0)) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) x0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0))) -> (hreal_mul (hreal_of_num (NUMERAL 0)) x0) = (hreal_of_num (NUMERAL 0)).
Definition term14 := forall y0 : hreal, forall y1 : hreal, (hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) y0) y1) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) y1) (hreal_mul y0 y1)).
Definition term1 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, ((hreal_add x0 y1) = (hreal_add y0 y1)) = (x0 = y0).
Definition term18 (x0 : hreal) := (fun y0 : hreal => (hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL (BIT1 0)))) y0) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) y0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y0))) x0.
Definition term25 (x0 : hreal) := @eq hreal (hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL (BIT1 0)))) x0).
Definition term28 (x0 : hreal) := imp ((hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) x0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0))).
Definition term27 (x0 : hreal) := imp ((hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL (BIT1 0)))) x0) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) x0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0))).
Definition term23 := hreal_mul (hreal_of_num (NUMERAL (BIT1 0))).
Definition term7 := fun y0 : hreal => y0 = (hreal_add (hreal_of_num (NUMERAL 0)) y0).
Definition term10 (x0 : hreal) := (fun y0 : hreal => y0 = (hreal_add (hreal_of_num (NUMERAL 0)) y0)) x0.
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, ((hreal_add x0 y1) = (hreal_add y0 y1)) = (x0 = y0)) x1.
Definition term29 (x0 : hreal) := hreal_mul (hreal_of_num (NUMERAL 0)) x0.
Definition term22 := hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL (BIT1 0)))).
Definition term20 (x0 : hreal) := hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) x0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0).
Definition term36 (x0 : hreal) := imp ((hreal_of_num (NUMERAL 0)) = (hreal_mul (hreal_of_num (NUMERAL 0)) x0)).
Definition term3 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, ((hreal_add x0 y0) = (hreal_add x1 y0)) = (x0 = x1).
Definition term33 (x0 : hreal) := @eq hreal (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0)).
Definition term6 := fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0.
Definition term32 (x0 : hreal) := hreal_add (hreal_of_num (NUMERAL 0)) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x0).
Definition term17 := forall y0 : hreal, (hreal_mul (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL (BIT1 0)))) y0) = (hreal_add (hreal_mul (hreal_of_num (NUMERAL 0)) y0) (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) y0)).
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y2) = (hreal_add y1 y2)) = (y0 = y1)) x0.
