Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (x0 : real) (x1 : real) := forall y0 : real, ((real_add x0 x1) = (real_add x0 y0)) = (x1 = y0).
Definition term4 := real_of_num (NUMERAL 0).
Definition term15 (x0 : real) (x1 : real) := real_add (real_add (real_neg x0) x0) x1.
Definition term18 (x0 : real) (x1 : real) := @eq real (real_add (real_neg x0) (real_add x0 x1)).
Definition term21 (x0 : real) (x1 : real) (x2 : real) := ((real_add (real_neg x0) (real_add x0 x1)) = (real_add (real_neg x0) (real_add x0 x2))) -> x1 = x2.
Definition term19 (x0 : real) (x1 : real) (x2 : real) := imp ((real_add (real_neg x1) (real_add x1 x0)) = (real_add (real_neg x1) (real_add x1 x2))).
Definition term25 (x0 : real) (x1 : real) (x2 : real) := (((real_add x1 x0) = (real_add x1 x2)) -> x0 = x2) /\ ((x0 = x2) -> (real_add x1 x0) = (real_add x1 x2)).
Definition term28 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2).
Definition term27 (x0 : real) := forall y0 : real, forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) = (y0 = y1).
Definition term6 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term16 (x0 : real) := real_add (real_add (real_neg x0) x0).
Definition term23 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) -> (real_add x1 x0) = (real_add x1 x2).
Definition term0 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term3 (x0 : real) := real_add (real_neg x0) x0.
Definition term8 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term9 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)) x2.
Definition term14 (x0 : real) (x1 : real) := real_add (real_neg x0) (real_add x0 x1).
Definition term2 (x0 : real) := (fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)) x1.
Definition term10 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term22 (x0 : real) (x1 : real) := (x0 = x1) -> x0 = x1.
Definition term1 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term13 (x0 : real) (x1 : real) := @eq real (real_add x0 x1).
Definition term12 (x0 : real) := real_add (real_neg x0).
Definition term11 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term17 := real_add (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) x0.
Definition term20 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term24 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 x1) = (real_add x0 x2)) -> x1 = x2.
