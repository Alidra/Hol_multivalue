Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : int) (x1 : nat) := imp ((~ (x1 = (NUMERAL 0))) /\ ((real_pow (real_of_int x0) x1) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term17 (x0 : int) (x1 : nat) := imp ((~ (x1 = (NUMERAL 0))) /\ ((int_pow x0 x1) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term2 (x0 : int) (x1 : nat) := (fun y0 : nat => ((~ (y0 = (NUMERAL 0))) /\ ((real_pow (real_of_int x0) y0) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_abs (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))) x1.
Definition term19 (x0 : int) := real_of_int (int_abs x0).
Definition term8 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ ((real_pow y0 y1) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_abs y0) = (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term15 (x0 : int) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ ((int_pow x0 x1) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term20 (x0 : int) := @eq real (real_abs (real_of_int x0)).
Definition term3 (x0 : nat) (x1 : int) := ((~ (x0 = (NUMERAL 0))) /\ ((real_pow (real_of_int x1) x0) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_abs (real_of_int x1)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term24 := forall y0 : int, forall y1 : nat, ((~ (y1 = (NUMERAL 0))) /\ ((int_pow y0 y1) = (int_of_num (NUMERAL (BIT1 0))))) -> (int_abs y0) = (int_of_num (NUMERAL (BIT1 0))).
Definition term4 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term13 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term22 (x0 : nat) (x1 : int) := ((~ (x0 = (NUMERAL 0))) /\ ((int_pow x1 x0) = (int_of_num (NUMERAL (BIT1 0))))) -> (int_abs x1) = (int_of_num (NUMERAL (BIT1 0))).
Definition term14 (x0 : int) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ ((real_pow (real_of_int x0) x1) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term9 := real_of_num (NUMERAL (BIT1 0)).
Definition term6 (x0 : int) (x1 : nat) := @eq real (real_pow (real_of_int x0) x1).
Definition term7 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_pow x0 x1)).
Definition term10 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term18 (x0 : int) := real_abs (real_of_int x0).
Definition term5 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term23 (x0 : int) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ ((int_pow x0 y0) = (int_of_num (NUMERAL (BIT1 0))))) -> (int_abs x0) = (int_of_num (NUMERAL (BIT1 0))).
Definition term1 (x0 : int) := forall y0 : nat, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow (real_of_int x0) y0) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_abs (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term12 := int_of_num (NUMERAL (BIT1 0)).
Definition term21 (x0 : int) := @eq real (real_of_int (int_abs x0)).
Definition term11 := NUMERAL (BIT1 0).
