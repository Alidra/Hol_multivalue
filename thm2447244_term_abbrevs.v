Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := int_of_num (NUMERAL 0).
Definition term1 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (x1 = (int_of_num (NUMERAL 0))).
Definition term0 (x0 : int) (x1 : int) := (fun y0 : int => ((x0 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_of_num (NUMERAL 0)))) = ((int_mul x0 y0) = (int_of_num (NUMERAL 0)))) x1.
