Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) (x1 : real) := (fun y0 : real => ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) y0))) -> real_lt (real_pow (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow y0 x0)) x1.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => real_le (real_of_num (NUMERAL 0)) (real_of_num y0)) x0.
Definition term13 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term24 (x0 : real) (x1 : nat) := real_lt (real_pow (real_of_num (NUMERAL (BIT1 0))) x1) (real_pow x0 x1).
Definition term20 (x0 : nat) (x1 : real) := (~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x1)).
Definition term26 (x0 : real) (x1 : nat) := True -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term30 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1)) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term18 := and (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term19 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term1 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term32 (x0 : nat) := forall y0 : real, ((~ (x0 = (NUMERAL 0))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) y0)) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 x0).
Definition term4 (x0 : nat) := forall y0 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) y0))) -> real_lt (real_pow (real_of_num (NUMERAL (BIT1 0))) x0) (real_pow y0 x0).
Definition term9 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term22 (x0 : nat) := real_lt (real_pow (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term29 (x0 : real) (x1 : nat) := (((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x0))) -> real_lt (real_pow (real_of_num (NUMERAL (BIT1 0))) x1) (real_pow x0 x1)) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term11 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term33 := forall y0 : nat, forall y1 : real, ((~ (y0 = (NUMERAL 0))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) y1)) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow y1 y0).
Definition term31 (x0 : real) (x1 : nat) := ((~ (x1 = (NUMERAL 0))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x0)) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term28 (x0 : real) (x1 : nat) := imp (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1)).
Definition term23 := real_lt (real_of_num (NUMERAL (BIT1 0))).
Definition term6 (x0 : real) (x1 : nat) := ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x0))) -> real_lt (real_pow (real_of_num (NUMERAL (BIT1 0))) x1) (real_pow x0 x1).
Definition term15 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term27 (x0 : real) (x1 : nat) := imp (((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x0))) -> real_lt (real_pow (real_of_num (NUMERAL (BIT1 0))) x1) (real_pow x0 x1)).
Definition term21 (x0 : nat) (x1 : real) := imp ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x1))).
Definition term3 := real_of_num (NUMERAL (BIT1 0)).
Definition term12 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term2 (x0 : nat) := (fun y0 : real => forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term14 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term16 := real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term7 (x0 : nat) (x1 : real) := (~ (x0 = (NUMERAL 0))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x1).
Definition term8 (x0 : real) := real_lt (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term25 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term17 := NUMERAL (BIT1 0).
