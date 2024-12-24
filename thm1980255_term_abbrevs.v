Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) = (y0 = x0)) False.
Definition term11 := @eq Prop (~ False).
Definition term48 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : Prop) (x5 : Prop) := (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) = x4) -> (x4 -> ((~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = x5) -> (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = (x4 -> x5).
Definition term28 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term57 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> True.
Definition term9 (x0 : Prop) := ~ (~ x0).
Definition term55 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> ((~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = True.
Definition term27 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0))) x1.
Definition term49 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : Prop) := (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) = ((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3))) -> (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> ((~ (real_le (real_div x0 x3) (real_div x1 x2))) = (~ (real_le (real_mul x0 x2) (real_mul x1 x3)))) = x4) -> (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x1 x2))) = (~ (real_le (real_mul x0 x2) (real_mul x1 x3)))) = (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> x4).
Definition term53 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop (real_le (real_div x0 x1) (real_div x2 x3)).
Definition term6 (x0 : Prop) (x1 : Prop) := @eq Prop (((~ x0) = (~ x1)) = (x0 = x1)).
Definition term54 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop (real_le (real_mul x0 x1) (real_mul x2 x3)).
Definition term51 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x3) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_le (real_div x0 x3) (real_div x2 x1)) = (real_le (real_mul x0 x1) (real_mul x2 x3)).
Definition term25 := forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term24 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term3 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) = (y0 = x0)) x1.
Definition term34 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_lt (real_mul x0 x1) (real_mul x2 x3).
Definition term52 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term18 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term41 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term16 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_le (real_mul x0 x1) (real_mul x2 x3).
Definition term20 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) = (real_lt y0 x0).
Definition term35 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ (real_le (real_div x0 x1) (real_div x2 x3)).
Definition term13 (x0 : Prop) := @eq Prop (~ x0).
Definition term56 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> ((~ (real_le (real_div x0 x3) (real_div x1 x2))) = (~ (real_le (real_mul x0 x2) (real_mul x1 x3)))) = True) -> (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x1 x2))) = (~ (real_le (real_mul x0 x2) (real_mul x1 x3)))) = (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> True).
Definition term22 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) = (real_lt y1 y0).
Definition term26 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) x0.
Definition term5 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) = (~ x0)) = (y0 = x0)) x1).
Definition term31 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x3) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_lt (real_div x0 x3) (real_div x2 x1)) = (real_lt (real_mul x0 x1) (real_mul x2 x3)).
Definition term50 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : Prop) := (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> ((~ (real_le (real_div x0 x3) (real_div x1 x2))) = (~ (real_le (real_mul x0 x2) (real_mul x1 x3)))) = x4) -> (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x1 x2))) = (~ (real_le (real_mul x0 x2) (real_mul x1 x3)))) = (((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> x4).
Definition term14 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term46 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : Prop) := forall y0 : Prop, (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) = x4) -> (x4 -> ((~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = y0) -> (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = (x4 -> y0).
Definition term42 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term8 := @eq Prop (~ True).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term29 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term44 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := forall y0 : Prop, forall y1 : Prop, (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) = y0) -> (y0 -> ((~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = y1) -> (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = (y0 -> y1).
Definition term43 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term36 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop (real_lt (real_div x0 x1) (real_div x2 x3)).
Definition term39 (x0 : real) (x1 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term21 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term38 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ (real_le (real_mul x0 x1) (real_mul x2 x3)).
Definition term47 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) = x4) -> (x4 -> ((~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = y0) -> (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = (x4 -> y0)) x5.
Definition term32 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term2 (x0 : Prop) := fun y0 : Prop => ((~ y0) = (~ x0)) = (y0 = x0).
Definition term12 (x0 : Prop) := @eq Prop ((~ False) = (~ x0)).
Definition term10 (x0 : Prop) := @eq Prop ((~ True) = (~ x0)).
Definition term17 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term15 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_le (real_div x0 x1) (real_div x2 x3).
Definition term19 (x0 : real) := fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term37 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop (~ (real_le (real_div x0 x1) (real_div x2 x3))).
Definition term40 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3))).
Definition term30 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt (real_of_num (NUMERAL 0)) x3) -> (real_lt (real_of_num (NUMERAL 0)) x1) -> (real_lt (real_div x0 x3) (real_div x2 x1)) = (real_lt (real_mul x0 x1) (real_mul x2 x3)).
Definition term4 (x0 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) = (y0 = x0)) True.
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term45 (x0 : real) (x1 : real) (x2 : real) (x3 : real) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) = y0) -> (y0 -> ((~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = y1) -> (((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (~ (real_le (real_div x0 x3) (real_div x2 x1))) = (~ (real_le (real_mul x0 x1) (real_mul x2 x3)))) = (y0 -> y1)) x4.
Definition term33 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_lt (real_div x0 x1) (real_div x2 x3).
Definition term23 := fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
