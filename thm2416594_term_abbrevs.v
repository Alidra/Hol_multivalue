Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := (fun y0 : int => forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1))) x0.
Definition term2 (x0 : int) := forall y0 : int, (int_sub x0 y0) = (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)).
Definition term0 := forall y0 : int, forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)).
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => (int_sub x0 y0) = (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0))) x1.
Definition term4 (x0 : int) (x1 : int) := int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1).
