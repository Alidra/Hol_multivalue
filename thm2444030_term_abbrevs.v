Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 := fun y0 : int => forall y1 : int, (y0 = y1) = ((int_sub y0 y1) = (int_of_num (NUMERAL 0))).
Definition term2 (x0 : int) := fun y0 : int => (x0 = y0) = ((int_sub x0 y0) = (int_of_num (NUMERAL 0))).
Definition term0 := int_of_num (NUMERAL 0).
Definition term9 (x0 : int) := (fun y0 : int => forall y1 : int, (y0 = y1) = ((int_sub y0 y1) = (int_of_num (NUMERAL 0)))) x0.
Definition term10 (x0 : int) (x1 : int) := (fun y0 : int => (x0 = y0) = ((int_sub x0 y0) = (int_of_num (NUMERAL 0)))) x1.
Definition term3 (x0 : int) := forall y0 : int, ((int_sub x0 y0) = (int_of_num (NUMERAL 0))) = (x0 = y0).
Definition term8 := forall y0 : int, forall y1 : int, (y0 = y1) = ((int_sub y0 y1) = (int_of_num (NUMERAL 0))).
Definition term7 := forall y0 : int, forall y1 : int, ((int_sub y0 y1) = (int_of_num (NUMERAL 0))) = (y0 = y1).
Definition term5 := fun y0 : int => forall y1 : int, ((int_sub y0 y1) = (int_of_num (NUMERAL 0))) = (y0 = y1).
Definition term4 (x0 : int) := forall y0 : int, (x0 = y0) = ((int_sub x0 y0) = (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := fun y0 : int => ((int_sub x0 y0) = (int_of_num (NUMERAL 0))) = (x0 = y0).
