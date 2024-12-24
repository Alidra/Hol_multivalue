Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term2 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term11 := real_neg (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term16 (x0 : int) := real_mul (real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term15 := real_mul (real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0))))).
Definition term6 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_int x0).
Definition term20 := int_neg (int_of_num (NUMERAL (BIT1 0))).
Definition term22 := forall y0 : int, (int_neg y0) = (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term19 (x0 : int) := real_of_int (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term14 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term10 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term5 (x0 : int) := @eq real (real_of_int (int_neg x0)).
Definition term1 (x0 : int) := real_neg (real_of_int x0).
Definition term21 (x0 : int) := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term12 := real_of_int (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : int) := @eq real (real_neg (real_of_int x0)).
Definition term7 := real_of_num (NUMERAL (BIT1 0)).
Definition term18 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term3 (x0 : int) := real_of_int (int_neg x0).
Definition term8 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term13 := int_of_num (NUMERAL (BIT1 0)).
Definition term9 := NUMERAL (BIT1 0).
