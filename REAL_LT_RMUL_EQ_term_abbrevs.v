Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (x0 : real) (x1 : real) := @eq Prop (~ (real_le x0 x1)).
Definition term13 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_le (real_mul x0 y0) (real_mul x1 y0)) = (real_le x0 x1)) x2.
Definition term34 (x0 : real) (x1 : real) (x2 : real) := ~ (real_le (real_mul x0 x2) (real_mul x1 x2)).
Definition term29 := real_of_num (NUMERAL 0).
Definition term32 (x0 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) -> (real_le x0 (real_of_num (NUMERAL 0))) = False.
Definition term37 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) -> ((real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = True.
Definition term45 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0))) x1.
Definition term42 := fun y0 : real => True.
Definition term33 (x0 : real) := real_le x0 (real_of_num (NUMERAL 0)).
Definition term44 := forall y0 : real, True.
Definition term46 (x0 : Prop) := forall y0 : real, x0.
Definition term40 (x0 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) -> True.
Definition term50 := forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_mul y0 y2) (real_mul y1 y2)) = (real_lt y0 y1).
Definition term48 (x0 : real) := forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) -> (real_lt (real_mul x0 y1) (real_mul y0 y1)) = (real_lt x0 y0).
Definition term10 (x0 : real) := forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) -> (real_le (real_mul x0 y1) (real_mul y0 y1)) = (real_le x0 y0).
Definition term8 := forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term7 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2).
Definition term24 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((real_lt (real_of_num (NUMERAL 0)) x0) = y0) -> (y0 -> ((real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = y1) -> ((real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = (y0 -> y1)) x3.
Definition term30 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) := ((real_lt (real_of_num (NUMERAL 0)) x2) = (~ (real_le x2 (real_of_num (NUMERAL 0))))) -> ((~ (real_le x2 (real_of_num (NUMERAL 0)))) -> ((real_lt (real_mul x0 x2) (real_mul x1 x2)) = (real_lt x0 x1)) = x3) -> ((real_lt (real_of_num (NUMERAL 0)) x2) -> (real_lt (real_mul x0 x2) (real_mul x1 x2)) = (real_lt x0 x1)) = ((~ (real_le x2 (real_of_num (NUMERAL 0)))) -> x3).
Definition term1 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term41 (x0 : real) (x1 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt (real_mul x0 y0) (real_mul x1 y0)) = (real_lt x0 x1).
Definition term27 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := ((real_lt (real_of_num (NUMERAL 0)) x0) = x3) -> (x3 -> ((real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = x4) -> ((real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = (x3 -> x4).
Definition term47 (x0 : real) := fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) -> (real_lt (real_mul x0 y1) (real_mul y0 y1)) = (real_lt x0 y0).
Definition term3 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term5 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term17 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) x0.
Definition term25 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) := forall y0 : Prop, ((real_lt (real_of_num (NUMERAL 0)) x0) = x3) -> (x3 -> ((real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = y0) -> ((real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = (x3 -> y0).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term22 (x0 : real) (x1 : real) (x2 : real) := forall y0 : Prop, forall y1 : Prop, ((real_lt (real_of_num (NUMERAL 0)) x0) = y0) -> (y0 -> ((real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = y1) -> ((real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = (y0 -> y1).
Definition term21 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term35 (x0 : real) (x1 : real) (x2 : real) := @eq Prop (real_lt (real_mul x0 x2) (real_mul x1 x2)).
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) -> (real_le (real_mul x0 y1) (real_mul y0 y1)) = (real_le x0 y0)) x1.
Definition term16 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x0 x2) (real_mul x1 x2).
Definition term14 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> (real_le (real_mul x1 x0) (real_mul x2 x0)) = (real_le x1 x2).
Definition term4 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term26 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((real_lt (real_of_num (NUMERAL 0)) x0) = x3) -> (x3 -> ((real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = y0) -> ((real_lt (real_of_num (NUMERAL 0)) x0) -> (real_lt (real_mul x1 x0) (real_mul x2 x0)) = (real_lt x1 x2)) = (x3 -> y0)) x4.
Definition term43 (x0 : real) (x1 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_lt (real_mul x0 y0) (real_mul x1 y0)) = (real_lt x0 x1).
Definition term12 (x0 : real) (x1 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> (real_le (real_mul x0 y0) (real_mul x1 y0)) = (real_le x0 x1).
Definition term15 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term31 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) := ((~ (real_le x2 (real_of_num (NUMERAL 0)))) -> ((real_lt (real_mul x0 x2) (real_mul x1 x2)) = (real_lt x0 x1)) = x3) -> ((real_lt (real_of_num (NUMERAL 0)) x2) -> (real_lt (real_mul x0 x2) (real_mul x1 x2)) = (real_lt x0 x1)) = ((~ (real_le x2 (real_of_num (NUMERAL 0)))) -> x3).
Definition term23 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_mul x0 x2) (real_mul x1 x2).
Definition term49 := fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_mul y0 y2) (real_mul y1 y2)) = (real_lt y0 y1).
Definition term0 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term2 (x0 : real) := fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le x2 (real_of_num (NUMERAL 0)))) -> ((real_lt (real_mul x0 x2) (real_mul x1 x2)) = (real_lt x0 x1)) = True) -> ((real_lt (real_of_num (NUMERAL 0)) x2) -> (real_lt (real_mul x0 x2) (real_mul x1 x2)) = (real_lt x0 x1)) = ((~ (real_le x2 (real_of_num (NUMERAL 0)))) -> True).
Definition term28 (x0 : real) := ~ (real_le x0 (real_of_num (NUMERAL 0))).
Definition term9 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_le (real_mul y0 y2) (real_mul y1 y2)) = (real_le y0 y1)) x0.
Definition term6 := fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
