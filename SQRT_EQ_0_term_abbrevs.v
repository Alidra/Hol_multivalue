Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := real_of_num (NUMERAL 0).
Definition term16 := and (forall y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term15 := and (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0)))).
Definition term8 := and (forall y0 : real, (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0)))).
Definition term7 := and (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term18 (x0 : real) := real_lt x0 (real_of_num (NUMERAL 0)).
Definition term39 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term37 := fun y0 : real => True.
Definition term12 := fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term34 (x0 : real) := @eq real (real_sgn (sqrt x0)).
Definition term38 := forall y0 : real, True.
Definition term40 (x0 : Prop) := forall y0 : real, x0.
Definition term4 := fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0))).
Definition term20 := fun y0 : real => (real_lt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term26 := (forall y0 : real, (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (forall y0 : real, (real_lt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term25 := (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0))))).
Definition term11 := fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0))).
Definition term10 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term31 := fun y0 : real => ((real_sgn (sqrt y0)) = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0))).
Definition term24 := (forall y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (forall y0 : real, (real_lt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term23 := (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0)))).
Definition term30 := fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term3 := fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term33 := forall y0 : real, ((real_sgn (sqrt y0)) = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0))).
Definition term22 := forall y0 : real, (real_lt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term14 := forall y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 := forall y0 : real, (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0))).
Definition term17 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term35 (x0 : real) := @eq real (real_sgn x0).
Definition term29 (x0 : real) := @eq Prop ((real_sgn (sqrt x0)) = (real_of_num (NUMERAL 0))).
Definition term1 (x0 : real) := real_sgn (sqrt x0).
Definition term28 (x0 : real) := @eq Prop ((sqrt x0) = (real_of_num (NUMERAL 0))).
Definition term19 := fun y0 : real => ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0))).
Definition term27 (x0 : real) := (fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0)))) x0.
Definition term9 := real_of_num (NUMERAL (BIT1 0)).
Definition term32 := forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term21 := forall y0 : real, ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0))).
Definition term13 := forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0))).
Definition term5 := forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real) := (fun y0 : real => (real_sgn (sqrt y0)) = (real_sgn y0)) x0.
Definition term36 (x0 : real) := @eq Prop ((real_sgn x0) = (real_of_num (NUMERAL 0))).
