Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term45 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_sub (real_mul x0 x2) (real_mul x1 x2)).
Definition term26 (x0 : real) := forall y0 : real, ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0).
Definition term72 (x0 : real) (x1 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0)).
Definition term17 := real_of_num (NUMERAL 0).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := imp ((~ ((real_sub x2 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) /\ ((real_sub (real_mul x0 x2) (real_mul x1 x2)) = (real_of_num (NUMERAL 0)))).
Definition term43 (x0 : real) (x1 : real) (x2 : real) := ((~ ((real_sub x0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) /\ ((real_sub (real_mul x1 x0) (real_mul x2 x0)) = (real_of_num (NUMERAL 0)))) -> (real_sub x1 x2) = (real_of_num (NUMERAL 0)).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_sub x2 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) /\ ((real_sub (real_mul x0 x2) (real_mul x1 x2)) = (real_of_num (NUMERAL 0))).
Definition term44 (x0 : real) := @eq real (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term64 (x0 : real) (x1 : real) := imp ((~ True) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ True)).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_sub x0 x1) x2.
Definition term47 (x0 : real) (x1 : real) (x2 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ (x2 = (real_of_num (NUMERAL 0))).
Definition term73 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 y0) = (real_mul x1 y0))) -> x0 = x1.
Definition term40 (x0 : real) (x1 : real) (x2 : real) := imp ((~ (x2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 x2) = (real_mul x1 x2))).
Definition term35 (x0 : real) := ~ ((real_sub x0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term75 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (y2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul y0 y2) = (real_mul y1 y2))) -> y0 = y1.
Definition term74 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (y1 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 y1) = (real_mul y0 y1))) -> x0 = y0.
Definition term31 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0))).
Definition term30 := forall y0 : real, forall y1 : real, ((real_sub y0 y1) = (real_of_num (NUMERAL 0))) = (y0 = y1).
Definition term13 := forall y0 : real, forall y1 : real, forall y2 : real, (real_sub (real_mul y0 y2) (real_mul y1 y2)) = (real_mul (real_sub y0 y1) y2).
Definition term12 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2)).
Definition term9 (x0 : real) := forall y0 : real, forall y1 : real, (real_sub (real_mul x0 y1) (real_mul y0 y1)) = (real_mul (real_sub x0 y0) y1).
Definition term8 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1)).
Definition term23 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term68 (x0 : real) (x1 : real) := (~ False) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ False).
Definition term67 (x0 : real) (x1 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ False.
Definition term1 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul x0 x2) (real_mul x1 x2).
Definition term57 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((fun y0 : Prop => ((~ y0) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ y0)) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0))) (x2 = (real_of_num (NUMERAL 0)))).
Definition term34 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term18 (x0 : real) (x1 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term29 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0))).
Definition term6 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1)).
Definition term51 (x0 : real) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (real_of_num (NUMERAL 0))).
Definition term5 (x0 : real) (x1 : real) := forall y0 : real, (real_sub (real_mul x0 y0) (real_mul x1 y0)) = (real_mul (real_sub x0 x1) y0).
Definition term15 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term49 (x0 : real) (x1 : real) (x2 : real) := imp ((~ (x2 = (real_of_num (NUMERAL 0)))) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ (x2 = (real_of_num (NUMERAL 0))))).
Definition term61 := and (~ True).
Definition term28 := fun y0 : real => forall y1 : real, ((real_sub y0 y1) = (real_of_num (NUMERAL 0))) = (y0 = y1).
Definition term7 (x0 : real) := fun y0 : real => forall y1 : real, (real_sub (real_mul x0 y1) (real_mul y0 y1)) = (real_mul (real_sub x0 y0) y1).
Definition term53 (x0 : real) (x1 : real) := fun y0 : Prop => ((~ y0) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ y0)) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0)).
Definition term32 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0)))) x0.
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = (real_of_num (NUMERAL 0))))) x0.
Definition term33 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0)))) x1.
Definition term3 (x0 : real) (x1 : real) := fun y0 : real => (real_sub (real_mul x0 y0) (real_mul x1 y0)) = (real_mul (real_sub x0 x1) y0).
Definition term24 (x0 : real) := fun y0 : real => ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0).
Definition term54 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : Prop => ((~ y0) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ y0)) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0))) (x2 = (real_of_num (NUMERAL 0))).
Definition term58 (x0 : real) (x1 : real) (x2 : real) := @eq Prop (((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (((real_sub x1 x2) = (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0))))) -> (real_sub x1 x2) = (real_of_num (NUMERAL 0))).
Definition term20 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_sub (real_mul x0 y1) (real_mul y0 y1)) = (real_mul (real_sub x0 y0) y1)) x1.
Definition term55 (x0 : real) (x1 : real) := (fun y0 : Prop => ((~ y0) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ y0)) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0))) True.
Definition term2 (x0 : real) (x1 : real) := fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0)).
Definition term63 (x0 : real) (x1 : real) := (~ True) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ True).
Definition term70 (x0 : real) (x1 : real) := imp ((~ False) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ False)).
Definition term11 := fun y0 : real => forall y1 : real, forall y2 : real, (real_sub (real_mul y0 y2) (real_mul y1 y2)) = (real_mul (real_sub y0 y1) y2).
Definition term10 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2)).
Definition term60 (x0 : real) (x1 : real) := ((~ False) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ False)) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0)).
Definition term21 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_sub (real_mul x0 y0) (real_mul x1 y0)) = (real_mul (real_sub x0 x1) y0)) x2.
Definition term50 (x0 : real) (x1 : real) (x2 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ (((real_sub x1 x2) = (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0))))) -> (real_sub x1 x2) = (real_of_num (NUMERAL 0)).
Definition term62 (x0 : real) (x1 : real) := ((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ True.
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0))))) x1.
Definition term56 (x0 : real) (x1 : real) := ((~ True) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ True)) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0)).
Definition term25 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0))).
Definition term71 (x0 : real) (x1 : real) := imp ((real_sub x0 x1) = (real_of_num (NUMERAL 0))).
Definition term66 := and (~ False).
Definition term59 (x0 : real) (x1 : real) := (fun y0 : Prop => ((~ y0) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ y0)) -> (real_sub x0 x1) = (real_of_num (NUMERAL 0))) False.
Definition term65 (x0 : real) (x1 : real) := False -> (real_sub x0 x1) = (real_of_num (NUMERAL 0)).
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0)).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = (real_of_num (NUMERAL 0)))) /\ (((real_sub x0 x1) = (real_of_num (NUMERAL 0))) \/ (x2 = (real_of_num (NUMERAL 0)))).
Definition term37 (x0 : real) := and (~ ((real_sub x0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))).
Definition term42 (x0 : real) (x1 : real) (x2 : real) := ((~ (x0 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x1 x0) = (real_mul x2 x0))) -> x1 = x2.
Definition term22 (x0 : real) := (fun y0 : real => (real_sub y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term36 (x0 : real) := and (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term46 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_mul (real_sub x0 x1) x2).
Definition term19 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_sub (real_mul y0 y2) (real_mul y1 y2)) = (real_mul (real_sub y0 y1) y2)) x0.
Definition term52 (x0 : real) := ((x0 = (real_of_num (NUMERAL 0))) = True) \/ ((x0 = (real_of_num (NUMERAL 0))) = False).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 x2) = (real_mul x1 x2)).
Definition term27 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0))).
Definition term69 (x0 : real) (x1 : real) := True /\ ((real_sub x0 x1) = (real_of_num (NUMERAL 0))).
