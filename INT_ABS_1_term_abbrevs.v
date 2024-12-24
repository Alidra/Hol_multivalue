Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 := @eq real (real_of_int (int_abs (int_of_num (NUMERAL (BIT1 0))))).
Definition term7 (x0 : int) := real_of_int (int_abs x0).
Definition term12 := int_abs (int_of_num (NUMERAL (BIT1 0))).
Definition term0 (x0 : nat) := real_of_int (int_of_num x0).
Definition term5 := real_abs (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term4 := real_abs (real_of_num (NUMERAL (BIT1 0))).
Definition term10 := @eq real (real_abs (real_of_num (NUMERAL (BIT1 0)))).
Definition term1 := real_of_num (NUMERAL (BIT1 0)).
Definition term2 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term6 (x0 : int) := real_abs (real_of_int x0).
Definition term8 := real_of_int (int_abs (int_of_num (NUMERAL (BIT1 0)))).
Definition term9 := int_of_num (NUMERAL (BIT1 0)).
Definition term3 := NUMERAL (BIT1 0).
