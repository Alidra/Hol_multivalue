Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> True.
Definition term22 (x0 : real) (x1 : real) (x2 : Prop) := (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) = ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1))) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = x2) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> x2).
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 y0)) x1.
Definition term35 := fun y0 : real => True.
Definition term32 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1).
Definition term37 := forall y0 : real, True.
Definition term39 (x0 : Prop) := forall y0 : real, x0.
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term41 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div y0 y1).
Definition term28 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term36 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 y0).
Definition term8 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term24 := real_lt (real_of_num (NUMERAL 0)).
Definition term34 (x0 : real) := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 y0).
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term40 := fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div y0 y1).
Definition term4 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) x0.
Definition term31 (x0 : real) (x1 : real) := (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = True) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> True).
Definition term20 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) = x2) -> (x2 -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = y0) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = (x2 -> y0)) x3.
Definition term29 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) (real_inv x1)).
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term10 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term11 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term12 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term19 (x0 : real) (x1 : real) (x2 : Prop) := forall y0 : Prop, (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) = x2) -> (x2 -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = y0) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = (x2 -> y0).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term1 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term16 (x0 : real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) = y0) -> (y0 -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = y1) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = (y0 -> y1).
Definition term15 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term17 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1).
Definition term23 (x0 : real) (x1 : real) (x2 : Prop) := (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = x2) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> x2).
Definition term25 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_mul x0 (real_inv x1)).
Definition term6 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term21 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) = x2) -> (x2 -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = x3) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = (x2 -> x3).
Definition term5 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term30 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = True.
Definition term26 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1)) = True.
Definition term3 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term18 (x0 : real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) = y0) -> (y0 -> (real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = y1) -> (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_div x0 x1)) = (y0 -> y1)) x2.
Definition term27 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) (real_inv x1))) -> (real_lt (real_of_num (NUMERAL 0)) (real_mul x0 (real_inv x1))) = True.
