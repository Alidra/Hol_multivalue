Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term7 (x0 : int) := real_mul (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term2 (x0 : nat) := real_of_int (int_of_num x0).
Definition term12 (x0 : int) := @eq real (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term15 := forall y0 : int, (int_mul y0 (int_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term13 (x0 : int) := @eq real (real_of_int (int_mul x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term14 (x0 : int) := int_mul x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term0 (x0 : int) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) (real_of_int x0).
Definition term3 := real_of_num (NUMERAL (BIT1 0)).
Definition term10 (x0 : int) := real_of_int (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term9 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term4 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term6 (x0 : int) := real_mul (real_of_int x0).
Definition term11 := int_of_num (NUMERAL (BIT1 0)).
Definition term5 := NUMERAL (BIT1 0).