Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term45 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) /\ True.
Definition term23 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_mul x0 x1))).
Definition term29 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term7 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term15 := real_of_num (NUMERAL 0).
Definition term43 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term8 := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) -> forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term5 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term17 (x0 : real) := and ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_of_num (NUMERAL 0)) = x0))).
Definition term12 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (x0 = x1)).
Definition term47 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term0 := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term32 (x0 : real) (x1 : real) := imp (((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (~ (x1 = (real_of_num (NUMERAL 0)))))).
Definition term16 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term46 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term2 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term27 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term19 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_of_num (NUMERAL 0)) = x0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (~ ((real_of_num (NUMERAL 0)) = x1))).
Definition term42 (x0 : real) (x1 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term28 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term35 (x0 : real) (x1 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)).
Definition term21 (x0 : real) (x1 : real) := imp (((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_of_num (NUMERAL 0)) = x0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (~ ((real_of_num (NUMERAL 0)) = x1)))).
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0)) x1.
Definition term37 (x0 : real) (x1 : real) := (((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (~ (x1 = (real_of_num (NUMERAL 0)))))) -> (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) /\ (~ ((real_mul x0 x1) = (real_of_num (NUMERAL 0)))).
Definition term40 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term34 (x0 : real) (x1 : real) := ~ ((real_mul x0 x1) = (real_of_num (NUMERAL 0))).
Definition term25 (x0 : real) (x1 : real) := (((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_of_num (NUMERAL 0)) = x0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (~ ((real_of_num (NUMERAL 0)) = x1)))) -> (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_mul x0 x1))).
Definition term39 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = (real_of_num (NUMERAL 0))))) x0.
Definition term9 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term6 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term24 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term38 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term18 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term22 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term14 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_of_num (NUMERAL 0)) = x0)).
Definition term20 (x0 : real) (x1 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term36 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) /\ (~ ((real_mul x0 x1) = (real_of_num (NUMERAL 0)))).
Definition term13 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term31 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (~ (x1 = (real_of_num (NUMERAL 0))))).
Definition term26 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = x0).
Definition term41 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0))))) x1.
Definition term4 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term44 (x0 : real) := or (x0 = (real_of_num (NUMERAL 0))).
Definition term30 (x0 : real) := and ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term33 (x0 : real) (x1 : real) := ~ ((real_of_num (NUMERAL 0)) = (real_mul x0 x1)).
Definition term10 (x0 : real) := forall y0 : real, (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0))).
