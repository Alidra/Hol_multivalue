Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0.
Definition term30 (x0 : real -> Prop) := ~ (all x0).
Definition term88 := (~ False) -> False.
Definition term11 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term36 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (~ ((sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)).
Definition term77 (x0 : Prop) := ~ (~ x0).
Definition term21 (x0 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = y0.
Definition term60 (x0 : real) (x1 : real) := (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((sqrt x0) = x1)).
Definition term33 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) x0.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term65 (x0 : real) (x1 : real) := ((sqrt x0) = x1) \/ ((~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term82 (x0 : real) (x1 : real) := imp (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)))).
Definition term10 := ~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0).
Definition term71 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term66 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ ((sqrt x0) = x1))).
Definition term57 (x0 : Prop) := (~ x0) -> x0.
Definition term41 (x0 : real) (x1 : real) := or (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term38 (x0 : real) (x1 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term74 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term53 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term49 := forall y0 : real, forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((sqrt y0) = y1).
Definition term17 := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1.
Definition term68 (x0 : real) (x1 : real) := (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term45 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term62 (x0 : real) (x1 : real) := ((sqrt x0) = x1) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term52 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ ((sqrt x0) = x1)).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term25 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0.
Definition term58 (x0 : real) := (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term56 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term32 := exists y0 : real, ~ ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) -> (sqrt (real_pow y1 (NUMERAL (BIT0 (BIT1 0))))) = y1) y0).
Definition term54 (x0 : real) (x1 : real) := ~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term39 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term81 (x0 : real) (x1 : real) := ~ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term80 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term15 := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term40 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term16 := ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term13 := (((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term73 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term72 (x0 : real) (x1 : real) := (~ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)))) -> (sqrt x0) = x1.
Definition term84 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term61 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((sqrt x0) = x1).
Definition term59 (x0 : real) := ~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term48 := fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((sqrt y0) = y1).
Definition term23 := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1.
Definition term43 (x0 : real) (x1 : real) := (~ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = x1).
Definition term29 (x0 : real) := sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term31 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term44 (x0 : real) (x1 : real) := ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = x1).
Definition term50 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y1)) \/ (~ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0))) \/ ((sqrt y0) = y1)) x0.
Definition term46 (x0 : real) := fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = y0).
Definition term42 (x0 : real) (x1 : real) := or ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term28 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term22 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = y0.
Definition term9 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> False.
Definition term83 (x0 : real) (x1 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term27 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0)).
Definition term86 (x0 : real) := (~ ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0)) -> (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term51 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = y0)) x1.
Definition term79 (x0 : real) := and (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term63 (x0 : real) (x1 : real) := or (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term26 (x0 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) -> (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0).
Definition term87 (x0 : real) := ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) -> False.
Definition term24 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term69 (x0 : real) (x1 : real) := or ((sqrt x0) = x1).
Definition term37 := exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (~ ((sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)).
Definition term64 (x0 : real) (x1 : real) := (~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ (((sqrt x0) = x1) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term55 (x0 : real) := ~ ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0).
Definition term75 (x0 : real) (x1 : real) := ~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term19 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term34 (x0 : real) := ~ ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) x0).
Definition term35 := fun y0 : real => ~ ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) -> (sqrt (real_pow y1 (NUMERAL (BIT0 (BIT1 0))))) = y1) y0).
Definition term85 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term76 (x0 : real) (x1 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) /\ (~ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term67 (x0 : real) (x1 : real) := @eq Prop (((sqrt x0) = x1) \/ ((~ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)))).
Definition term12 := ((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term14 := (((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> ((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) -> (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> False.
Definition term47 (x0 : real) := forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0))) \/ ((sqrt x0) = y0).
Definition term78 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term20 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = x1.
Definition term70 (x0 : real) (x1 : real) := ((sqrt x1) = x0) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1))).
Definition term18 := imp (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)).
