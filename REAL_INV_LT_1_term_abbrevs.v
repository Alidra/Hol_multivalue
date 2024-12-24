Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (x0 : real) := real_lt (real_inv x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term4 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x0)) -> real_lt (real_inv x0) (real_inv x1).
Definition term16 (x0 : real) := real_lt (real_inv x0).
Definition term5 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1).
Definition term21 := and (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term10 := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y0)) -> real_lt (real_inv y0) (real_inv y1).
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 x0)) -> real_lt (real_inv x0) (real_inv y0)) x1.
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_inv y0) (real_inv x0)) x1.
Definition term9 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y0)) -> real_lt (real_inv y0) (real_inv y1).
Definition term0 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0).
Definition term20 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 x0)) -> real_lt (real_inv x0) (real_inv y0).
Definition term2 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_inv y0) (real_inv x0).
Definition term23 (x0 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) -> real_lt (real_inv x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term11 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y0)) -> real_lt (real_inv y0) (real_inv y1)) x0.
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) x0.
Definition term18 (x0 : real) := real_lt (real_inv x0) (real_inv (real_of_num (NUMERAL (BIT1 0)))).
Definition term7 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0)) -> real_lt (real_inv x0) (real_inv x1).
Definition term19 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x0)) -> real_lt (real_inv x0) (real_inv (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 (x0 : real) (x1 : real) := real_lt (real_inv x0) (real_inv x1).
Definition term22 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term14 := real_of_num (NUMERAL (BIT1 0)).
Definition term13 := real_inv (real_of_num (NUMERAL (BIT1 0))).
Definition term15 (x0 : real) := real_lt (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term24 := forall y0 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) y0) -> real_lt (real_inv y0) (real_of_num (NUMERAL (BIT1 0))).
