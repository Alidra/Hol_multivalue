Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 := fun y0 : int => forall y1 : int, ((y0 = (int_of_num (NUMERAL 0))) \/ (y1 = (int_of_num (NUMERAL 0)))) = ((int_mul y0 y1) = (int_of_num (NUMERAL 0))).
Definition term6 := fun y0 : int => forall y1 : int, ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ (y1 = (int_of_num (NUMERAL 0)))).
Definition term5 (x0 : int) := forall y0 : int, ((x0 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_of_num (NUMERAL 0)))) = ((int_mul x0 y0) = (int_of_num (NUMERAL 0))).
Definition term0 := int_of_num (NUMERAL 0).
Definition term10 (x0 : int) := (fun y0 : int => forall y1 : int, ((y0 = (int_of_num (NUMERAL 0))) \/ (y1 = (int_of_num (NUMERAL 0)))) = ((int_mul y0 y1) = (int_of_num (NUMERAL 0)))) x0.
Definition term1 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (x1 = (int_of_num (NUMERAL 0))).
Definition term3 (x0 : int) := fun y0 : int => ((x0 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_of_num (NUMERAL 0)))) = ((int_mul x0 y0) = (int_of_num (NUMERAL 0))).
Definition term4 (x0 : int) := forall y0 : int, ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) = ((x0 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_of_num (NUMERAL 0)))).
Definition term9 := forall y0 : int, forall y1 : int, ((y0 = (int_of_num (NUMERAL 0))) \/ (y1 = (int_of_num (NUMERAL 0)))) = ((int_mul y0 y1) = (int_of_num (NUMERAL 0))).
Definition term8 := forall y0 : int, forall y1 : int, ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) = ((y0 = (int_of_num (NUMERAL 0))) \/ (y1 = (int_of_num (NUMERAL 0)))).
Definition term2 (x0 : int) := fun y0 : int => ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) = ((x0 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_of_num (NUMERAL 0)))).
Definition term11 (x0 : int) (x1 : int) := (fun y0 : int => ((x0 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_of_num (NUMERAL 0)))) = ((int_mul x0 y0) = (int_of_num (NUMERAL 0)))) x1.
