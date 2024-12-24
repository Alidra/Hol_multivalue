Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term17 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term23 (x0 : int) (x1 : int) := real_of_int (int_abs (int_sub x0 x1)).
Definition term40 (x0 : int) (x1 : int) (x2 : int) := real_lt (real_of_int (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x1)))) (real_of_int (int_sub x1 x2)).
Definition term34 (x0 : int) (x1 : int) (x2 : int) := real_lt (real_of_int (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x2)))) (real_of_int (int_sub x1 x2)).
Definition term19 (x0 : int) (x1 : int) := real_abs (real_sub (real_of_int x0) (real_of_int x1)).
Definition term26 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term36 (x0 : int) (x1 : int) := int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x1)).
Definition term39 (x0 : int) (x1 : int) (x2 : int) := real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x0) (real_of_int x1)))) (real_sub (real_of_int x1) (real_of_int x2)).
Definition term33 (x0 : int) (x1 : int) (x2 : int) := real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x0) (real_of_int x2)))) (real_sub (real_of_int x1) (real_of_int x2)).
Definition term24 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x0) (real_of_int x1))).
Definition term7 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((real_lt (real_of_int x1) (real_of_int x0)) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x2) (real_of_int x1)))) (real_sub (real_of_int x0) (real_of_int x1))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x3) (real_of_int x0)))) (real_sub (real_of_int x0) (real_of_int x1))))) -> real_lt (real_of_int x2) (real_of_int x3).
Definition term25 (x0 : int) (x1 : int) := real_mul (real_of_int (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int (int_abs (int_sub x0 x1))).
Definition term20 (x0 : int) (x1 : int) := real_abs (real_of_int (int_sub x0 x1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_int x0) y1) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y0 (real_of_int x0)))) (real_sub y1 (real_of_int x0))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y2 y1))) (real_sub y1 (real_of_int x0))))) -> real_lt y0 y2) (real_of_int x1).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, forall y1 : real, ((real_lt (real_of_int x0) y0) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x1) (real_of_int x0)))) (real_sub y0 (real_of_int x0))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y1 y0))) (real_sub y0 (real_of_int x0))))) -> real_lt (real_of_int x1) y1.
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_int x0) y1) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y0 (real_of_int x0)))) (real_sub y1 (real_of_int x0))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y2 y1))) (real_sub y1 (real_of_int x0))))) -> real_lt y0 y2.
Definition term22 (x0 : int) := real_of_int (int_abs x0).
Definition term15 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term13 := real_of_int (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term41 (x0 : int) (x1 : int) (x2 : int) := int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x1))) (int_sub x1 x2).
Definition term35 (x0 : int) (x1 : int) (x2 : int) := int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x2))) (int_sub x1 x2).
Definition term46 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((real_lt (real_of_int x3) (real_of_int x2)) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x0) (real_of_int x3)))) (real_sub (real_of_int x2) (real_of_int x3))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x1) (real_of_int x2)))) (real_sub (real_of_int x2) (real_of_int x3))))).
Definition term47 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((int_lt x3 x2) /\ ((int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x3))) (int_sub x2 x3)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x1 x2))) (int_sub x2 x3)))).
Definition term6 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : real => ((real_lt (real_of_int x1) (real_of_int x0)) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x2) (real_of_int x1)))) (real_sub (real_of_int x0) (real_of_int x1))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y0 (real_of_int x0)))) (real_sub (real_of_int x0) (real_of_int x1))))) -> real_lt (real_of_int x2) y0) (real_of_int x3).
Definition term38 (x0 : int) (x1 : int) (x2 : int) := and (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x2))) (int_sub x1 x2)).
Definition term11 (x0 : nat) := real_of_int (int_of_num x0).
Definition term28 (x0 : int) (x1 : int) := real_of_int (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x1))).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y2) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y1 y0))) (real_sub y2 y0)) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y3 y2))) (real_sub y2 y0)))) -> real_lt y1 y3) (real_of_int x0).
Definition term10 (x0 : int) (x1 : int) := and (int_lt x0 x1).
Definition term32 (x0 : int) (x1 : int) := real_lt (real_of_int (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x1)))).
Definition term37 (x0 : int) (x1 : int) (x2 : int) := and (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x0) (real_of_int x2)))) (real_sub (real_of_int x1) (real_of_int x2))).
Definition term8 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term9 (x0 : int) (x1 : int) := and (real_lt (real_of_int x0) (real_of_int x1)).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_int x0) y0) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x1) (real_of_int x0)))) (real_sub y0 (real_of_int x0))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y1 y0))) (real_sub y0 (real_of_int x0))))) -> real_lt (real_of_int x1) y1) (real_of_int x2).
Definition term52 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((int_lt y0 y2) /\ ((int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub y1 y0))) (int_sub y2 y0)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub y3 y2))) (int_sub y2 y0)))) -> int_lt y1 y3.
Definition term51 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((int_lt x0 y1) /\ ((int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub y0 x0))) (int_sub y1 x0)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub y2 y1))) (int_sub y1 x0)))) -> int_lt y0 y2.
Definition term50 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((int_lt x0 y0) /\ ((int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x1 x0))) (int_sub y0 x0)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub y1 y0))) (int_sub y0 x0)))) -> int_lt x1 y1.
Definition term5 (x0 : int) (x1 : int) (x2 : int) := forall y0 : real, ((real_lt (real_of_int x1) (real_of_int x0)) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x2) (real_of_int x1)))) (real_sub (real_of_int x0) (real_of_int x1))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y0 (real_of_int x0)))) (real_sub (real_of_int x0) (real_of_int x1))))) -> real_lt (real_of_int x2) y0.
Definition term12 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term14 := NUMERAL (BIT0 (BIT1 0)).
Definition term16 := real_mul (real_of_int (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term44 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (real_lt (real_of_int x3) (real_of_int x2)) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x0) (real_of_int x3)))) (real_sub (real_of_int x2) (real_of_int x3))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x1) (real_of_int x2)))) (real_sub (real_of_int x2) (real_of_int x3)))).
Definition term48 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((int_lt x1 x0) /\ ((int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x2 x1))) (int_sub x0 x1)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x3 x0))) (int_sub x0 x1)))) -> int_lt x2 x3.
Definition term49 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((int_lt x1 x0) /\ ((int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x2 x1))) (int_sub x0 x1)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub y0 x0))) (int_sub x0 x1)))) -> int_lt x2 y0.
Definition term31 (x0 : int) (x1 : int) := real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x0) (real_of_int x1)))).
Definition term42 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x0) (real_of_int x3)))) (real_sub (real_of_int x2) (real_of_int x3))) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub (real_of_int x1) (real_of_int x2)))) (real_sub (real_of_int x2) (real_of_int x3))).
Definition term29 := int_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term27 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term21 (x0 : int) := real_abs (real_of_int x0).
Definition term30 (x0 : int) (x1 : int) := int_abs (int_sub x0 x1).
Definition term45 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x3 x2) /\ ((int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x3))) (int_sub x2 x3)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x1 x2))) (int_sub x2 x3))).
Definition term43 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x0 x3))) (int_sub x2 x3)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x1 x2))) (int_sub x2 x3)).
