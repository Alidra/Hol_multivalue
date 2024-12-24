Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (x0 : real) (x1 : real) (x2 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2).
Definition term18 := real_of_num (NUMERAL 0).
Definition term60 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term32 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_mul x1 x0) (real_mul x1 x2)) \/ ((real_mul x1 x0) = (real_mul x1 x2)).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ ((real_lt (real_mul x0 x1) (real_mul x0 x2)) \/ (x1 = x2)).
Definition term14 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 y1) (real_mul y0 y2))) -> real_lt y1 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y2 y0) (real_mul y2 y1))) -> real_lt y0 y1.
Definition term17 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (real_of_num (NUMERAL 0))).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ ((real_lt (real_mul x0 x1) (real_mul x0 x2)) \/ (x1 = x2))) -> (real_lt x1 x2) \/ (x1 = x2).
Definition term66 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term31 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term43 (x0 : real) := ~ (real_lt x0 x0).
Definition term71 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_mul y0 y1) (real_mul y0 y2))) -> real_le y1 y2.
Definition term70 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_mul x0 y0) (real_mul x0 y1))) -> real_le y0 y1.
Definition term22 (x0 : real) := forall y0 : real, forall y1 : real, ((real_mul x0 y0) = (real_mul x0 y1)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)).
Definition term13 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y2 y0) (real_mul y2 y1))) -> real_lt y0 y1.
Definition term2 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 y0) (real_mul x0 y1))) -> real_lt y0 y1.
Definition term0 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 y1) (real_mul y0 y2))) -> real_lt y1 y2.
Definition term36 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_le (real_mul x1 x0) (real_mul x1 x2)).
Definition term35 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term8 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 y1) (real_mul y0 y2))) -> real_lt y1 y2) -> real_lt x0 x1.
Definition term50 (x0 : real) (x1 : real) := real_lt (real_mul x0 x1).
Definition term20 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term45 := real_lt (real_of_num (NUMERAL 0)).
Definition term24 (x0 : real) (x1 : real) := forall y0 : real, ((real_mul x0 x1) = (real_mul x0 y0)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = y0)).
Definition term51 (x0 : real) := real_lt (real_mul (real_of_num (NUMERAL 0)) x0).
Definition term61 (x0 : real) (x1 : real) := False \/ (x0 = x1).
Definition term33 (x0 : real) (x1 : real) (x2 : real) := or (real_lt (real_mul x1 x0) (real_mul x1 x2)).
Definition term64 (x0 : real) (x1 : real) (x2 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x0) /\ ((real_lt (real_mul x0 x1) (real_mul x0 x2)) \/ (x1 = x2))).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ ((real_lt (real_mul x0 x1) (real_mul x0 x2)) \/ ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2)))) -> (real_lt x1 x2) \/ (x1 = x2).
Definition term12 (x0 : real) := forall y0 : real, (exists y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul y1 x0) (real_mul y1 y0))) -> real_lt x0 y0.
Definition term9 (x0 : real) (x1 : real) := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 x0) (real_mul y0 x1)).
Definition term55 := @eq real (real_of_num (NUMERAL 0)).
Definition term44 (x0 : real) := (~ (real_lt x0 x0)) -> (real_lt x0 x0) = False.
Definition term40 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_mul x0 x1) (real_mul x0 x2))) -> real_le x1 x2.
Definition term59 (x0 : real) (x1 : real) := False -> (real_lt x0 x1) \/ (x0 = x1).
Definition term25 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_mul x0 x1) = (real_mul x0 y0)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = y0))) x2.
Definition term27 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) x0.
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y2 y0) (real_mul y2 y1))) -> real_lt y0 y1) x0.
Definition term6 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 x1) (real_mul x0 x2))) -> real_lt x1 x2.
Definition term37 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ ((real_lt (real_mul x0 x1) (real_mul x0 x2)) \/ ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2))).
Definition term11 (x0 : real) (x1 : real) := (exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 x0) (real_mul y0 x1))) -> real_lt x0 x1.
Definition term34 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_mul x0 x1) (real_mul x0 x2)) \/ ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2)).
Definition term62 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_mul x0 x1) (real_mul x0 x2)) \/ (x1 = x2).
Definition term19 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term48 := real_mul (real_of_num (NUMERAL 0)).
Definition term47 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term54 (x0 : real) (x1 : real) := or (real_lt (real_mul (real_of_num (NUMERAL 0)) x0) (real_mul (real_of_num (NUMERAL 0)) x1)).
Definition term23 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_mul x0 y0) = (real_mul x0 y1)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = y1))) x1.
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 y0) (real_mul x0 y1))) -> real_lt y0 y1) x1.
Definition term38 (x0 : real) (x1 : real) (x2 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_le (real_mul x1 x0) (real_mul x1 x2))).
Definition term46 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term57 (x0 : real) (x1 : real) := True \/ (x0 = x1).
Definition term10 (x0 : real) (x1 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 x0) (real_mul y0 x1)).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul y1 x0) (real_mul y1 y0))) -> real_lt x0 y0) x1.
Definition term58 (x0 : real) (x1 : real) := (real_lt (real_mul (real_of_num (NUMERAL 0)) x0) (real_mul (real_of_num (NUMERAL 0)) x1)) \/ True.
Definition term69 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_mul x0 x1) (real_mul x0 y0))) -> real_le x1 y0.
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 x1) (real_mul x0 y0))) -> real_lt x1 y0.
Definition term30 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ (x0 = x1).
Definition term29 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0))) x1.
Definition term53 (x0 : real) (x1 : real) := real_lt (real_mul (real_of_num (NUMERAL 0)) x0) (real_mul (real_of_num (NUMERAL 0)) x1).
Definition term49 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term7 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt (real_mul x1 x0) (real_mul x1 x2)).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_mul x1 x0) (real_mul x1 x2).
Definition term56 (x0 : real) := or (x0 = (real_of_num (NUMERAL 0))).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x0) /\ ((real_lt (real_mul x0 x1) (real_mul x0 x2)) \/ ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2)))).
Definition term28 (x0 : real) := forall y0 : real, (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0)).
Definition term68 (x0 : real) := (real_lt x0 x0) \/ True.
Definition term5 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x0 x1) (real_mul x0 y0))) -> real_lt x1 y0) x2.
Definition term21 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_mul y0 y1) = (real_mul y0 y2)) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = y2))) x0.
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul y0 y1) (real_mul y0 y2))) -> real_lt y1 y2) x0.
Definition term42 (x0 : real) := (fun y0 : real => ~ (real_lt y0 y0)) x0.
Definition term67 (x0 : real) := or (real_lt x0 x0).
