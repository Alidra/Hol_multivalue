Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)).
Definition term8 (x0 : Prop) := forall y0 : Prop, (y0 -> x0) = ((~ x0) -> ~ y0).
Definition term49 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ True.
Definition term27 (x0 : real) (x1 : real) := (~ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ (~ (~ (x1 = (real_of_num (NUMERAL 0))))).
Definition term29 (x0 : Prop) := ~ (~ x0).
Definition term31 := real_of_num (NUMERAL 0).
Definition term14 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x0) = ((~ x0) -> ~ y0)) x1.
Definition term7 (x0 : Prop) := forall y0 : Prop, ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term9 := fun y0 : Prop => forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0).
Definition term20 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (((~ (x2 = (real_of_num (NUMERAL 0)))) /\ (~ (x3 = (real_of_num (NUMERAL 0))))) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)))) -> ((~ (x2 = (real_of_num (NUMERAL 0)))) /\ (~ (x3 = (real_of_num (NUMERAL 0))))) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term25 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term3 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term13 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1)) x0.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term24 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term42 (x0 : real) := ~ (real_lt x0 x0).
Definition term17 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_div x0 x1) (real_div x2 x3).
Definition term1 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term46 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term10 := fun y0 : Prop => forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1).
Definition term28 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term4 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term44 := real_lt (real_of_num (NUMERAL 0)).
Definition term34 (x0 : real) (x1 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term37 (x0 : real) (x1 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term19 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (((~ (x2 = (real_of_num (NUMERAL 0)))) /\ (~ (x3 = (real_of_num (NUMERAL 0))))) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3)))) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term43 (x0 : real) := (~ (real_lt x0 x0)) -> (real_lt x0 x0) = False.
Definition term22 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))).
Definition term47 (x0 : real) := or (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term38 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term23 (x0 : real) (x1 : real) := (~ ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))))) -> ~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term21 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term12 := forall y0 : Prop, forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1).
Definition term11 := forall y0 : Prop, forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0).
Definition term45 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term35 (x0 : real) (x1 : real) := imp (~ ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))))).
Definition term39 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term26 (x0 : real) (x1 : real) := ~ ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0))))).
Definition term5 (x0 : Prop) := fun y0 : Prop => ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term33 (x0 : real) := or (x0 = (real_of_num (NUMERAL 0))).
Definition term15 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((~ (x2 = (real_of_num (NUMERAL 0)))) /\ (~ (x3 = (real_of_num (NUMERAL 0))))) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term16 (x0 : real) (x1 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = (real_of_num (NUMERAL 0)))).
Definition term40 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0)))) -> (~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term36 (x0 : real) (x1 : real) := imp ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0)))).
Definition term32 (x0 : real) := or (~ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term48 (x0 : real) := True \/ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term41 (x0 : real) := (fun y0 : real => ~ (real_lt y0 y0)) x0.
Definition term30 (x0 : real) := ~ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term6 (x0 : Prop) := fun y0 : Prop => (y0 -> x0) = ((~ x0) -> ~ y0).
