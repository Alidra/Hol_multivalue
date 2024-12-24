Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term43 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = x2)).
Definition term5 (x0 : real) (x1 : real) (x2 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2).
Definition term75 := (~ False) -> False.
Definition term45 (x0 : real) (x1 : real) (x2 : real) := ~ ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0)))).
Definition term10 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_mul x0 x2) = (real_mul x1 x2)).
Definition term13 (x0 : real) (x1 : real) := fun y0 : real => ((real_mul x0 y0) = (real_mul x1 y0)) = ((x0 = x1) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term39 (x0 : Prop) := ~ (~ x0).
Definition term44 := real_of_num (NUMERAL 0).
Definition term55 (x0 : real) (x1 : real) (x2 : real) := or (((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) /\ ((~ (x0 = x1)) /\ (~ (x2 = (real_of_num (NUMERAL 0)))))).
Definition term50 (x0 : real) (x1 : real) (x2 : real) := ((~ (x2 = (real_of_num (NUMERAL 0)))) /\ (~ (x0 = x1))) /\ ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0)))).
Definition term54 (x0 : real) (x1 : real) (x2 : real) := or (((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) /\ (~ ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0)))))).
Definition term64 (x0 : real) := @eq Prop ((fun y0 : real => ~ (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term32 (x0 : Prop) := (~ x0) -> False.
Definition term66 (x0 : real) := fun y0 : real => ~ (y0 = x0).
Definition term40 (x0 : real) (x1 : real) (x2 : real) := (~ (((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) = ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0)))))) -> False.
Definition term7 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term76 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term73 (x0 : Prop) := (~ x0) -> x0.
Definition term60 := fun y0 : real => ~ (y0 = (real_of_num (NUMERAL 0))).
Definition term49 (x0 : real) (x1 : real) (x2 : real) := (~ ((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1))) /\ ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0)))).
Definition term31 := forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))).
Definition term29 (x0 : real) := forall y0 : real, forall y1 : real, ((y1 = (real_of_num (NUMERAL 0))) \/ (x0 = y0)) = ((x0 = y0) \/ (y1 = (real_of_num (NUMERAL 0)))).
Definition term24 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_mul y2 y0) = (real_mul y2 y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))).
Definition term23 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_mul y0 y2) = (real_mul y1 y2)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))).
Definition term20 (x0 : real) := forall y0 : real, forall y1 : real, ((real_mul y1 x0) = (real_mul y1 y0)) = ((x0 = y0) \/ (y1 = (real_of_num (NUMERAL 0)))).
Definition term19 (x0 : real) := forall y0 : real, forall y1 : real, ((real_mul x0 y1) = (real_mul y0 y1)) = ((x0 = y0) \/ (y1 = (real_of_num (NUMERAL 0)))).
Definition term1 (x0 : real) := forall y0 : real, forall y1 : real, ((real_mul x0 y0) = (real_mul x0 y1)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)).
Definition term51 (x0 : real) (x1 : real) (x2 : real) := and ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2)).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := ~ (((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) = ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0))))).
Definition term62 := (fun y0 : real => ~ (y0 = (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term58 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term3 (x0 : real) (x1 : real) := forall y0 : real, ((real_mul x0 x1) = (real_mul x0 y0)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = y0)).
Definition term77 (x0 : real) := (x0 = x0) -> False.
Definition term28 (x0 : real) := fun y0 : real => forall y1 : real, ((y1 = (real_of_num (NUMERAL 0))) \/ (x0 = y0)) = ((x0 = y0) \/ (y1 = (real_of_num (NUMERAL 0)))).
Definition term18 (x0 : real) := fun y0 : real => forall y1 : real, ((real_mul y1 x0) = (real_mul y1 y0)) = ((x0 = y0) \/ (y1 = (real_of_num (NUMERAL 0)))).
Definition term17 (x0 : real) := fun y0 : real => forall y1 : real, ((real_mul x0 y1) = (real_mul y0 y1)) = ((x0 = y0) \/ (y1 = (real_of_num (NUMERAL 0)))).
Definition term25 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2)).
Definition term47 (x0 : real) (x1 : real) (x2 : real) := and (~ ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2))).
Definition term59 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term34 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0))))).
Definition term68 (x0 : real) := (fun y0 : real => ~ (y0 = x0)) x0.
Definition term35 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False.
Definition term27 (x0 : real) (x1 : real) := forall y0 : real, ((y0 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) = ((x0 = x1) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term16 (x0 : real) (x1 : real) := forall y0 : real, ((real_mul y0 x0) = (real_mul y0 x1)) = ((x0 = x1) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term15 (x0 : real) (x1 : real) := forall y0 : real, ((real_mul x0 y0) = (real_mul x1 y0)) = ((x0 = x1) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term72 := (~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)).
Definition term53 (x0 : real) (x1 : real) (x2 : real) := ((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) /\ ((~ (x0 = x1)) /\ (~ (x2 = (real_of_num (NUMERAL 0))))).
Definition term4 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_mul x0 x1) = (real_mul x0 y0)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = y0))) x2.
Definition term42 (x0 : real) (x1 : real) (x2 : real) := ~ ((x0 = (real_of_num (NUMERAL 0))) \/ (x1 = x2)).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := and ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (~ (x1 = x2))).
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term65 (x0 : real) := @eq Prop (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term26 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) = ((x0 = x1) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term38 := ~ (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))).
Definition term56 (x0 : real) (x1 : real) (x2 : real) := (((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) /\ (~ ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0)))))) \/ ((~ ((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1))) /\ ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0))))).
Definition term33 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False.
Definition term11 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_mul x1 x0) = (real_mul x1 x2)).
Definition term36 := (((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False.
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_mul x0 y0) = (real_mul x0 y1)) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = y1))) x1.
Definition term67 (x0 : real) (x1 : real) := (fun y0 : real => ~ (y0 = x0)) x1.
Definition term30 := fun y0 : real => forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))).
Definition term22 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_mul y2 y0) = (real_mul y2 y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))).
Definition term21 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_mul y0 y2) = (real_mul y1 y2)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))).
Definition term9 (x0 : real) (x1 : real) := @eq real (real_mul x0 x1).
Definition term70 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => ~ (y0 = x0)) x1).
Definition term14 (x0 : real) (x1 : real) := fun y0 : real => ((real_mul y0 x0) = (real_mul y0 x1)) = ((x0 = x1) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term69 (x0 : real) := ~ (x0 = x0).
Definition term12 (x0 : real) (x1 : real) (x2 : real) := (x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0))).
Definition term57 (x0 : real) (x1 : real) (x2 : real) := (((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) /\ ((~ (x0 = x1)) /\ (~ (x2 = (real_of_num (NUMERAL 0)))))) \/ (((~ (x2 = (real_of_num (NUMERAL 0)))) /\ (~ (x0 = x1))) /\ ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0))))).
Definition term37 := (((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False) -> ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = (real_of_num (NUMERAL 0))) \/ (y0 = y1)) = ((y0 = y1) \/ (y2 = (real_of_num (NUMERAL 0)))))) -> False.
Definition term74 := ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) -> False.
Definition term61 (x0 : real) := (fun y0 : real => ~ (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_mul y0 y1) = (real_mul y0 y2)) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = y2))) x0.
Definition term71 (x0 : real) (x1 : real) := @eq Prop (~ (x0 = x1)).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := ((x2 = (real_of_num (NUMERAL 0))) \/ (x0 = x1)) /\ (~ ((x0 = x1) \/ (x2 = (real_of_num (NUMERAL 0))))).
Definition term63 := ~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term46 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) /\ (~ (x2 = (real_of_num (NUMERAL 0)))).
