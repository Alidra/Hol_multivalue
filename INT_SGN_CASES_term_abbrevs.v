Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) := real_sgn (real_of_int x0).
Definition term8 := real_of_int (int_of_num (NUMERAL 0)).
Definition term7 := real_of_num (NUMERAL 0).
Definition term9 := int_of_num (NUMERAL 0).
Definition term19 := real_neg (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : int) := (fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL 0))) \/ (((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) \/ ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_int x0).
Definition term10 (x0 : int) := or ((real_sgn (real_of_int x0)) = (real_of_num (NUMERAL 0))).
Definition term5 (x0 : int) := @eq real (real_of_int (int_sgn x0)).
Definition term16 (x0 : int) := or ((real_sgn (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term24 (x0 : int) := ((real_sgn (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))) \/ ((real_sgn (real_of_int x0)) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term6 (x0 : nat) := real_of_int (int_of_num x0).
Definition term23 := int_neg (int_of_num (NUMERAL (BIT1 0))).
Definition term1 (x0 : int) := ((real_sgn (real_of_int x0)) = (real_of_num (NUMERAL 0))) \/ (((real_sgn (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))) \/ ((real_sgn (real_of_int x0)) = (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term26 (x0 : int) := ((int_sgn x0) = (int_of_num (NUMERAL 0))) \/ (((int_sgn x0) = (int_of_num (NUMERAL (BIT1 0)))) \/ ((int_sgn x0) = (int_neg (int_of_num (NUMERAL (BIT1 0)))))).
Definition term11 (x0 : int) := or ((int_sgn x0) = (int_of_num (NUMERAL 0))).
Definition term18 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term27 := forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) \/ (((int_sgn y0) = (int_of_num (NUMERAL (BIT1 0)))) \/ ((int_sgn y0) = (int_neg (int_of_num (NUMERAL (BIT1 0)))))).
Definition term3 (x0 : int) := real_of_int (int_sgn x0).
Definition term4 (x0 : int) := @eq real (real_sgn (real_of_int x0)).
Definition term20 (x0 : int) := real_neg (real_of_int x0).
Definition term22 := real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term25 (x0 : int) := ((int_sgn x0) = (int_of_num (NUMERAL (BIT1 0)))) \/ ((int_sgn x0) = (int_neg (int_of_num (NUMERAL (BIT1 0))))).
Definition term17 (x0 : int) := or ((int_sgn x0) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term12 := real_of_num (NUMERAL (BIT1 0)).
Definition term21 (x0 : int) := real_of_int (int_neg x0).
Definition term13 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term15 := int_of_num (NUMERAL (BIT1 0)).
Definition term14 := NUMERAL (BIT1 0).
