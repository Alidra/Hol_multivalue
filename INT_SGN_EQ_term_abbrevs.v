Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) := real_sgn (real_of_int x0).
Definition term22 := real_of_int (int_of_num (NUMERAL 0)).
Definition term36 (x0 : int) (x1 : int) := real_gt (real_of_int x0) (real_of_int x1).
Definition term21 := real_of_num (NUMERAL 0).
Definition term27 := int_of_num (NUMERAL 0).
Definition term26 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term5 (x0 : int) := real_lt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term43 (x0 : int) := @eq Prop ((int_sgn x0) = (int_of_num (NUMERAL 0))).
Definition term13 := real_neg (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term39 := (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL (BIT1 0)))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) = (int_lt y0 (int_of_num (NUMERAL 0)))).
Definition term34 (x0 : int) := real_gt (real_of_int x0).
Definition term35 (x0 : int) := real_gt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term31 (x0 : int) := real_gt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term41 (x0 : int) := (fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term30 (x0 : int) := (fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term2 (x0 : int) := (fun y0 : real => ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term8 (x0 : int) := @eq real (real_of_int (int_sgn x0)).
Definition term9 (x0 : nat) := real_of_int (int_of_num x0).
Definition term18 := int_neg (int_of_num (NUMERAL (BIT1 0))).
Definition term19 (x0 : int) := @eq Prop ((real_sgn (real_of_int x0)) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term25 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term46 := (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL (BIT1 0)))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) = (int_lt y0 (int_of_num (NUMERAL 0))))).
Definition term0 := (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0)))).
Definition term20 (x0 : int) := @eq Prop ((int_sgn x0) = (int_neg (int_of_num (NUMERAL (BIT1 0))))).
Definition term24 (x0 : int) := real_lt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term4 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term33 (x0 : int) := @eq Prop ((int_sgn x0) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term6 (x0 : int) := real_of_int (int_sgn x0).
Definition term7 (x0 : int) := @eq real (real_sgn (real_of_int x0)).
Definition term42 (x0 : int) := @eq Prop ((real_sgn (real_of_int x0)) = (real_of_num (NUMERAL 0))).
Definition term14 (x0 : int) := real_neg (real_of_int x0).
Definition term37 (x0 : int) := int_gt x0 (int_of_num (NUMERAL 0)).
Definition term16 := real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term32 (x0 : int) := @eq Prop ((real_sgn (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term45 := forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0))).
Definition term38 := forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL (BIT1 0)))) = (int_gt y0 (int_of_num (NUMERAL 0))).
Definition term28 := forall y0 : int, ((int_sgn y0) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) = (int_lt y0 (int_of_num (NUMERAL 0))).
Definition term10 := real_of_num (NUMERAL (BIT1 0)).
Definition term40 := forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term29 := forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0))).
Definition term1 := forall y0 : real, ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0))).
Definition term23 (x0 : int) := real_lt (real_of_int x0).
Definition term15 (x0 : int) := real_of_int (int_neg x0).
Definition term11 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term44 (x0 : int) := @eq real (real_of_int x0).
Definition term17 := int_of_num (NUMERAL (BIT1 0)).
Definition term12 := NUMERAL (BIT1 0).
