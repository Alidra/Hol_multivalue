Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : real) := ~ ((real_mul x0 (real_of_num (NUMERAL (BIT1 0)))) = x0).
Definition term67 (x0 : real) := ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = (real_mul x0 (real_of_num (NUMERAL (BIT1 0))))) /\ ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = x0).
Definition term23 := fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term24 (x0 : real -> Prop) := ~ (all x0).
Definition term71 := (~ False) -> False.
Definition term11 := imp (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term59 (x0 : Prop) := ~ (~ x0).
Definition term31 := fun y0 : real => ~ ((real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0).
Definition term58 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term8 := (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False.
Definition term17 := fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term64 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term19 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term9 := ~ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term3 := ~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0).
Definition term34 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term52 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term41 (x0 : real) := (~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = x0)) -> (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = x0.
Definition term40 (x0 : Prop) := (~ x0) -> x0.
Definition term5 := ((~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False) -> (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False.
Definition term54 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term56 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term50 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term21 := forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term51 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term12 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False.
Definition term48 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term15 := (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> ~ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term70 (x0 : real) := ((real_mul x0 (real_of_num (NUMERAL (BIT1 0)))) = x0) -> False.
Definition term26 := exists y0 : real, ~ ((fun y1 : real => (real_mul y1 (real_of_num (NUMERAL (BIT1 0)))) = y1) y0).
Definition term36 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term35 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term45 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term30 := fun y0 : real => ~ ((fun y1 : real => (real_mul y1 (real_of_num (NUMERAL (BIT1 0)))) = y1) y0).
Definition term44 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term55 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term16 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term10 := forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term32 := exists y0 : real, ~ ((real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0).
Definition term6 := (((~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False) -> (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False) -> (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False.
Definition term20 := fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term25 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term33 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term2 := (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> False.
Definition term63 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term49 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term47 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term7 := (((~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False) -> (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False) -> ((~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False) -> (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False.
Definition term61 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term69 (x0 : real) := (~ ((real_mul x0 (real_of_num (NUMERAL (BIT1 0)))) = x0)) -> (real_mul x0 (real_of_num (NUMERAL (BIT1 0)))) = x0.
Definition term68 (x0 : real) := (((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = (real_mul x0 (real_of_num (NUMERAL (BIT1 0))))) /\ ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = x0)) -> (real_mul x0 (real_of_num (NUMERAL (BIT1 0)))) = x0.
Definition term18 (x0 : real) := fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0).
Definition term39 (x0 : real) := ~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = (real_mul x0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term1 := forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term66 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term57 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term37 := real_of_num (NUMERAL (BIT1 0)).
Definition term53 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term28 (x0 : real) := ~ ((fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0).
Definition term42 (x0 : real) := ~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = x0).
Definition term62 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term13 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> ~ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term22 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term38 (x0 : real) := (~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = (real_mul x0 (real_of_num (NUMERAL (BIT1 0)))))) -> (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = (real_mul x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term43 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term27 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term60 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term46 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term4 := (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) -> False.
Definition term14 := imp (~ (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0)).
