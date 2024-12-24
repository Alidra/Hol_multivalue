Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 := real_of_int (int_of_num (NUMERAL 0)).
Definition term4 := real_of_num (NUMERAL 0).
Definition term23 := int_of_num (NUMERAL 0).
Definition term3 (x0 : int) (x1 : int) := real_add (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_of_int x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => ((real_add (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (real_of_num (NUMERAL 0))) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) /\ (y0 = (real_of_num (NUMERAL 0))))) (real_of_int x1).
Definition term15 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term25 (x0 : int) (x1 : int) := @eq Prop ((int_add (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow x1 (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))).
Definition term20 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, ((real_add (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow y1 (NUMERAL (BIT0 (BIT1 0))))) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (y1 = (real_of_num (NUMERAL 0))))) (real_of_int x0).
Definition term14 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term29 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) /\ (x1 = (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := forall y0 : real, ((real_add (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (real_of_num (NUMERAL 0))) = (((real_of_int x0) = (real_of_num (NUMERAL 0))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term27 (x0 : int) := and ((real_of_int x0) = (real_of_num (NUMERAL 0))).
Definition term24 (x0 : int) (x1 : int) := @eq Prop ((real_add (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_of_int x1) (NUMERAL (BIT0 (BIT1 0))))) = (real_of_num (NUMERAL 0))).
Definition term5 (x0 : int) (x1 : int) := ((real_of_int x0) = (real_of_num (NUMERAL 0))) /\ ((real_of_int x1) = (real_of_num (NUMERAL 0))).
Definition term30 (x0 : int) := forall y0 : int, ((int_add (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = ((x0 = (int_of_num (NUMERAL 0))) /\ (y0 = (int_of_num (NUMERAL 0)))).
Definition term31 := forall y0 : int, forall y1 : int, ((int_add (int_pow y0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow y1 (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) /\ (y1 = (int_of_num (NUMERAL 0)))).
Definition term18 (x0 : int) (x1 : int) := @eq real (real_add (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_of_int x1) (NUMERAL (BIT0 (BIT1 0))))).
Definition term6 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term10 := NUMERAL (BIT0 (BIT1 0)).
Definition term22 (x0 : int) (x1 : int) := int_add (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term19 (x0 : int) (x1 : int) := @eq real (real_of_int (int_add (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term16 (x0 : int) (x1 : int) := real_of_int (int_add (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term13 (x0 : int) (x1 : int) := real_add (real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_of_int (int_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term11 (x0 : int) := real_add (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term12 (x0 : int) := real_add (real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term28 (x0 : int) := and (x0 = (int_of_num (NUMERAL 0))).
Definition term26 (x0 : int) := @eq real (real_of_int x0).
Definition term17 (x0 : int) := int_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term7 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term8 (x0 : int) := real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term9 (x0 : int) := real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
