Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (x0 : nat) := real_abs (real_of_num x0).
Definition term8 (x0 : real) (x1 : real) := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> (real_abs x0) = (real_abs x1).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) x0.
Definition term31 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term14 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2)) -> forall y0 : real, forall y1 : real, (exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ ((real_pow y0 y2) = (real_pow y1 y2))) -> (real_abs y0) = (real_abs y1).
Definition term12 (x0 : real) := forall y0 : real, (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_pow x0 y1) = (real_pow y0 y1))) -> (real_abs x0) = (real_abs y0).
Definition term41 := forall y0 : real, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ ((real_pow y0 y1) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_abs y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term13 := forall y0 : real, forall y1 : real, (exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ ((real_pow y0 y2) = (real_pow y1 y2))) -> (real_abs y0) = (real_abs y1).
Definition term2 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> (real_abs y0) = (real_abs y1).
Definition term25 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term21 := forall y0 : nat, (real_of_num y0) = (real_abs (real_of_num y0)).
Definition term18 := fun y0 : nat => (real_abs (real_of_num y0)) = (real_of_num y0).
Definition term37 (x0 : real) := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_pow x0 y0) = (real_pow (real_of_num (NUMERAL (BIT1 0))) y0)).
Definition term9 (x0 : real) (x1 : real) := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_pow x0 y0) = (real_pow x1 y0)).
Definition term38 (x0 : real) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_pow x0 y0) = (real_pow (real_of_num (NUMERAL (BIT1 0))) y0)).
Definition term5 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> (real_abs x1) = (real_abs y0)) x2.
Definition term22 (x0 : nat) := (fun y0 : nat => (real_of_num y0) = (real_abs (real_of_num y0))) x0.
Definition term29 (x0 : real) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_pow x0 y0) = (real_pow (real_of_num (NUMERAL (BIT1 0))) y0))) -> (real_abs x0) = (real_abs (real_of_num (NUMERAL (BIT1 0)))).
Definition term7 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term4 (x0 : nat) (x1 : real) := forall y0 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> (real_abs x1) = (real_abs y0).
Definition term19 := fun y0 : nat => (real_of_num y0) = (real_abs (real_of_num y0)).
Definition term0 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2).
Definition term28 (x0 : real) := @eq real (real_abs x0).
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ ((real_pow y0 y2) = (real_pow y1 y2))) -> (real_abs y0) = (real_abs y1)) x0.
Definition term26 := real_abs (real_of_num (NUMERAL (BIT1 0))).
Definition term36 (x0 : real) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ ((real_pow x0 x1) = (real_pow (real_of_num (NUMERAL (BIT1 0))) x1)).
Definition term11 (x0 : real) (x1 : real) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_pow x0 y0) = (real_pow x1 y0))) -> (real_abs x0) = (real_abs x1).
Definition term3 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> (real_abs y0) = (real_abs y1)) x1.
Definition term33 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term34 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term24 := real_of_num (NUMERAL (BIT1 0)).
Definition term30 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term20 := forall y0 : nat, (real_abs (real_of_num y0)) = (real_of_num y0).
Definition term32 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term35 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_pow x0 y1) = (real_pow y0 y1))) -> (real_abs x0) = (real_abs y0)) x1.
Definition term39 (x0 : nat) (x1 : real) := ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_abs x1) = (real_of_num (NUMERAL (BIT1 0))).
Definition term10 (x0 : real) (x1 : real) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_pow x0 y0) = (real_pow x1 y0)).
Definition term40 (x0 : real) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow x0 y0) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_abs x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term6 (x0 : nat) (x1 : real) (x2 : real) := ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow x2 x0))) -> (real_abs x1) = (real_abs x2).
Definition term27 := NUMERAL (BIT1 0).
Definition term23 (x0 : real) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ ((real_pow x0 x1) = (real_of_num (NUMERAL (BIT1 0)))).
