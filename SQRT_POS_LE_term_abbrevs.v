Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term21 (x0 : real -> Prop) := ~ (all x0).
Definition term54 := (~ False) -> False.
Definition term4 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False.
Definition term31 := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term48 (x0 : Prop) := ~ (~ x0).
Definition term28 := exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))).
Definition term51 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term9 := ~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term3 := ~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)).
Definition term18 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))).
Definition term15 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term33 (x0 : real) := ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term16 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0).
Definition term46 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term32 := forall y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term42 (x0 : Prop) := (~ x0) -> x0.
Definition term34 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term37 := forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term47 (x0 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term41 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term14 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term23 := exists y0 : real, ~ ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) -> real_le (real_of_num (NUMERAL 0)) (sqrt y1)) y0).
Definition term40 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term43 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term52 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term20 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term6 := (((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False.
Definition term39 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term53 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) -> False.
Definition term45 (x0 : real) := @eq Prop ((real_le (real_of_num (NUMERAL 0)) (sqrt x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term22 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term8 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False.
Definition term24 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) x0.
Definition term30 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term19 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term2 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> False.
Definition term27 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))).
Definition term10 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term35 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term1 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0).
Definition term12 := (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> ~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term13 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term44 (x0 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))).
Definition term25 (x0 : real) := ~ ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) x0).
Definition term26 := fun y0 : real => ~ ((fun y1 : real => (real_le (real_of_num (NUMERAL 0)) y1) -> real_le (real_of_num (NUMERAL 0)) (sqrt y1)) y0).
Definition term36 := fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)).
Definition term17 (x0 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term5 := ((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False.
Definition term7 := (((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False) -> ((~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False) -> (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> False.
Definition term38 (x0 : real) := (fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0))) x0.
Definition term49 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term11 := imp (~ (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0))).
Definition term50 (x0 : real) := imp (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
