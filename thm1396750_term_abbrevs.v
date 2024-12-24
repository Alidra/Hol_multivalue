Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := real_of_num (NUMERAL 0).
Definition term21 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = True.
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term7 (x0 : real) := forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term17 := fun y0 : real => True.
Definition term12 (x0 : real) (x1 : Prop) := ((x0 = (real_of_num (NUMERAL 0))) = (x0 = (real_of_num (NUMERAL 0)))) -> ((x0 = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = x1) -> ((x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) -> x1).
Definition term18 := forall y0 : real, True.
Definition term20 (x0 : Prop) := forall y0 : real, x0.
Definition term13 (x0 : real) (x1 : Prop) := ((x0 = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = x1) -> ((x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) -> x1).
Definition term22 (x0 : real) := ((x0 = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = True) -> ((x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) -> True).
Definition term10 (x0 : real) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((x0 = (real_of_num (NUMERAL 0))) = x1) -> (x1 -> (forall y1 : real, (real_mul y1 x0) = (real_of_num (NUMERAL 0))) = y0) -> ((x0 = (real_of_num (NUMERAL 0))) -> forall y1 : real, (real_mul y1 x0) = (real_of_num (NUMERAL 0))) = (x1 -> y0)) x2.
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term15 := @eq real (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term16 (x0 : real) := fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term9 (x0 : real) (x1 : Prop) := forall y0 : Prop, ((x0 = (real_of_num (NUMERAL 0))) = x1) -> (x1 -> (forall y1 : real, (real_mul y1 x0) = (real_of_num (NUMERAL 0))) = y0) -> ((x0 = (real_of_num (NUMERAL 0))) -> forall y1 : real, (real_mul y1 x0) = (real_of_num (NUMERAL 0))) = (x1 -> y0).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term6 (x0 : real) := forall y0 : Prop, forall y1 : Prop, ((x0 = (real_of_num (NUMERAL 0))) = y0) -> (y0 -> (forall y2 : real, (real_mul y2 x0) = (real_of_num (NUMERAL 0))) = y1) -> ((x0 = (real_of_num (NUMERAL 0))) -> forall y2 : real, (real_mul y2 x0) = (real_of_num (NUMERAL 0))) = (y0 -> y1).
Definition term5 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term14 (x0 : real) (x1 : real) := @eq real (real_mul x0 x1).
Definition term8 (x0 : real) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = (real_of_num (NUMERAL 0))) = y0) -> (y0 -> (forall y2 : real, (real_mul y2 x0) = (real_of_num (NUMERAL 0))) = y1) -> ((x0 = (real_of_num (NUMERAL 0))) -> forall y2 : real, (real_mul y2 x0) = (real_of_num (NUMERAL 0))) = (y0 -> y1)) x1.
Definition term1 (x0 : real) := real_mul x0 (real_of_num (NUMERAL 0)).
Definition term11 (x0 : real) (x1 : Prop) (x2 : Prop) := ((x0 = (real_of_num (NUMERAL 0))) = x1) -> (x1 -> (forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = x2) -> ((x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0))) = (x1 -> x2).
Definition term24 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> True.
Definition term23 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
