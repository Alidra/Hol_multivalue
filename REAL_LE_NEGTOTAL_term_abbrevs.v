Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : real) := or (real_le (real_of_num (NUMERAL 0)) x0).
Definition term13 := real_of_num (NUMERAL 0).
Definition term17 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term23 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term1 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term20 := fun y0 : real => True.
Definition term3 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term15 (x0 : real) := real_le x0 (real_of_num (NUMERAL 0)).
Definition term11 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term22 := forall y0 : real, True.
Definition term24 (x0 : Prop) := forall y0 : real, x0.
Definition term9 (x0 : real) (x1 : real) := real_le x0 (real_neg x1).
Definition term4 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 (real_neg y1)) = (real_le (real_add y0 y1) (real_of_num (NUMERAL 0)))) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term7 (x0 : real) := forall y0 : real, (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0))).
Definition term18 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_le x0 (real_of_num (NUMERAL 0))).
Definition term12 (x0 : real) := real_le (real_add (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0)))) x1.
Definition term10 (x0 : real) (x1 : real) := real_le (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term21 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg y0)).
Definition term14 (x0 : real) := real_le (real_add (real_of_num (NUMERAL 0)) x0).
Definition term19 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg y0)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.