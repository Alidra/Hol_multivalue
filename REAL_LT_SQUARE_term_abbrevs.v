Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term6 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term3 := real_of_num (NUMERAL 0).
Definition term24 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term13 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (x0 = x1)).
Definition term17 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = (real_mul x0 x0)).
Definition term5 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term18 (x0 : real) := True /\ (~ ((real_of_num (NUMERAL 0)) = (real_mul x0 x0))).
Definition term21 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term4 (x0 : real) (x1 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term9 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term20 (x0 : real) := @eq Prop (~ ((real_of_num (NUMERAL 0)) = (real_mul x0 x0))).
Definition term1 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term22 (x0 : real) := ~ ((real_mul x0 x0) = (real_of_num (NUMERAL 0))).
Definition term14 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term26 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y0)) = (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term10 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = (real_of_num (NUMERAL 0))))) x0.
Definition term25 (x0 : real) := @eq Prop (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term8 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) x0.
Definition term23 (x0 : real) := @eq Prop (~ ((real_mul x0 x0) = (real_of_num (NUMERAL 0)))).
Definition term16 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0))))) x1.
Definition term15 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_mul x0 x0))).
Definition term19 (x0 : real) := @eq Prop (real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x0)).
Definition term11 (x0 : real) := forall y0 : real, (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0))).
