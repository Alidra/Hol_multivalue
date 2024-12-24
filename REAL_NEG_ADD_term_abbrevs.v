Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term25 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_add x1 x0) = (real_add y0 x0)) -> x1 = y0) x2.
Definition term16 (x0 : real) (x1 : real) := forall y0 : real, ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1).
Definition term4 := real_of_num (NUMERAL 0).
Definition term32 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y1 y0) = (real_add y2 y0)) -> y1 = y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) -> y0 = y1.
Definition term27 (x0 : real) (x1 : real) := exists y0 : real, (real_add x0 y0) = (real_add x1 y0).
Definition term17 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1)) x2.
Definition term11 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_add (real_add x0 x1) (real_add x2 x3)).
Definition term28 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 y0) = (real_add x1 y0).
Definition term35 (x0 : real) (x1 : real) := (exists y0 : real, (real_add (real_neg (real_add x0 x1)) y0) = (real_add (real_add (real_neg x0) (real_neg x1)) y0)) -> (real_neg (real_add x0 x1)) = (real_add (real_neg x0) (real_neg x1)).
Definition term49 := forall y0 : real, forall y1 : real, (real_neg (real_add y0 y1)) = (real_add (real_neg y0) (real_neg y1)).
Definition term31 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) -> y0 = y1.
Definition term22 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y1 y0) = (real_add y2 y0)) -> y1 = y2.
Definition term21 (x0 : real) := forall y0 : real, forall y1 : real, ((real_add y0 x0) = (real_add y1 x0)) -> y0 = y1.
Definition term14 (x0 : real) := forall y0 : real, forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0).
Definition term41 (x0 : real) (x1 : real) := real_add (real_add (real_neg x0) (real_neg x1)) (real_add x0 x1).
Definition term26 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y1 y0) = (real_add y2 y0)) -> y1 = y2) -> x0 = x1.
Definition term43 (x0 : real) := real_add (real_add (real_neg x0) x0).
Definition term42 (x0 : real) (x1 : real) := real_add (real_add (real_neg x0) x0) (real_add (real_neg x1) x1).
Definition term0 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term6 (x0 : real) (x1 : real) (x2 : real) := ((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))).
Definition term3 (x0 : real) := real_add (real_neg x0) x0.
Definition term30 (x0 : real) := forall y0 : real, (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) -> x0 = y0.
Definition term47 (x0 : real) (x1 : real) := fun y0 : real => (real_add (real_neg (real_add x0 x1)) y0) = (real_add (real_add (real_neg x0) (real_neg x1)) y0).
Definition term40 := @eq real (real_of_num (NUMERAL 0)).
Definition term19 (x0 : real) (x1 : real) (x2 : real) := ((real_add x1 x0) = (real_add x2 x0)) -> x1 = x2.
Definition term9 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 x1) (real_add x2 x3).
Definition term33 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) -> y0 = y1) x0.
Definition term10 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add x0 (real_add x1 (real_add x2 x3)).
Definition term39 (x0 : real) (x1 : real) := @eq real (real_add (real_neg (real_add x0 x1)) (real_add x0 x1)).
Definition term38 (x0 : real) (x1 : real) := real_add (real_neg (real_add x0 x1)) (real_add x0 x1).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := (((real_add x1 x0) = (real_add x2 x0)) = (x1 = x2)) -> ((real_add x1 x0) = (real_add x2 x0)) -> x1 = x2.
Definition term36 (x0 : real) (x1 : real) := real_neg (real_add x0 x1).
Definition term2 (x0 : real) := (fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term12 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_add x0 (real_add x1 (real_add x2 x3))).
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_add y0 x0) = (real_add y1 x0)) -> y0 = y1) x1.
Definition term15 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0)) x1.
Definition term8 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term34 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) -> x0 = y0) x1.
Definition term48 (x0 : real) := forall y0 : real, (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0)).
Definition term1 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term20 (x0 : real) (x1 : real) := forall y0 : real, ((real_add x1 x0) = (real_add y0 x0)) -> x1 = y0.
Definition term46 (x0 : real) (x1 : real) := exists y0 : real, (real_add (real_neg (real_add x0 x1)) y0) = (real_add (real_add (real_neg x0) (real_neg x1)) y0).
Definition term37 (x0 : real) (x1 : real) := real_add (real_neg x0) (real_neg x1).
Definition term45 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term5 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term29 (x0 : real) (x1 : real) := (exists y0 : real, (real_add x0 y0) = (real_add x1 y0)) -> x0 = x1.
Definition term7 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term44 := real_add (real_of_num (NUMERAL 0)).
Definition term23 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y1 y0) = (real_add y2 y0)) -> y1 = y2) x0.
Definition term13 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) x0.
