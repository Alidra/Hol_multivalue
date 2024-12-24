Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : real) := @eq real (real_inv x0).
Definition term2 := fun y0 : real => y0 = (real_inv (real_inv y0)).
Definition term6 := real_of_num (NUMERAL 0).
Definition term4 := forall y0 : real, y0 = (real_inv (real_inv y0)).
Definition term7 := real_inv (real_of_num (NUMERAL 0)).
Definition term1 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term5 (x0 : real) := (fun y0 : real => y0 = (real_inv (real_inv y0))) x0.
Definition term3 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term10 (x0 : real) := @eq real (real_inv (real_inv x0)).
Definition term9 := @eq real (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) := real_inv (real_inv x0).
Definition term12 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> (real_inv x0) = (real_of_num (NUMERAL 0)).
Definition term11 := real_inv (real_inv (real_of_num (NUMERAL 0))).
Definition term15 := forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term14 (x0 : real) := (((real_inv x0) = (real_of_num (NUMERAL 0))) -> x0 = (real_of_num (NUMERAL 0))) /\ ((x0 = (real_of_num (NUMERAL 0))) -> (real_inv x0) = (real_of_num (NUMERAL 0))).
Definition term13 (x0 : real) := ((real_inv x0) = (real_of_num (NUMERAL 0))) -> x0 = (real_of_num (NUMERAL 0)).
