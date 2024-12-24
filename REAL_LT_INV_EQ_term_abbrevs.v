Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 := fun y0 : real => y0 = (real_inv (real_inv y0)).
Definition term6 := forall y0 : real, y0 = (real_inv (real_inv y0)).
Definition term13 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) -> real_lt (real_of_num (NUMERAL 0)) (real_inv (real_inv x0)).
Definition term3 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term7 (x0 : real) := (fun y0 : real => y0 = (real_inv (real_inv y0))) x0.
Definition term5 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term8 := real_lt (real_of_num (NUMERAL 0)).
Definition term1 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term16 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0).
Definition term2 (x0 : real) := real_inv (real_inv x0).
Definition term12 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term10 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_inv (real_inv x0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) x0.
Definition term9 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term14 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) -> real_lt (real_of_num (NUMERAL 0)) x0) /\ ((real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_inv x0)).
Definition term15 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term11 (x0 : real) := imp (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)).
