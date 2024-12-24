Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := real_of_num (NUMERAL 0).
Definition term14 := and (forall y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term13 := and (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0)))).
Definition term6 := and (forall y0 : real, (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0)))).
Definition term5 := and (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term45 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (sqrt y0)) = (real_lt (real_of_num (NUMERAL 0)) y0).
Definition term16 (x0 : real) := real_lt x0 (real_of_num (NUMERAL 0)).
Definition term49 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 (x0 : real) := fun y0 : real => (real_lt x0 y0) = (real_gt y0 x0).
Definition term46 := fun y0 : real => True.
Definition term10 := fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term43 (x0 : real) := @eq Prop ((real_sgn x0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term28 (x0 : real) := forall y0 : real, (real_lt x0 y0) = (real_gt y0 x0).
Definition term37 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) = (real_gt y0 x0)) x1.
Definition term40 (x0 : real) := @eq real (real_sgn (sqrt x0)).
Definition term48 := forall y0 : real, True.
Definition term27 (x0 : real) := forall y0 : real, (real_gt y0 x0) = (real_lt x0 y0).
Definition term50 (x0 : Prop) := forall y0 : real, x0.
Definition term32 := forall y0 : real, forall y1 : real, (real_lt y0 y1) = (real_gt y1 y0).
Definition term31 := forall y0 : real, forall y1 : real, (real_gt y1 y0) = (real_lt y0 y1).
Definition term2 := fun y0 : real => (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0))).
Definition term18 := fun y0 : real => (real_lt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term47 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (sqrt y0)) = (real_lt (real_of_num (NUMERAL 0)) y0).
Definition term24 := (forall y0 : real, (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (forall y0 : real, (real_lt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term23 := (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0))))).
Definition term9 := fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0))).
Definition term8 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term22 := (forall y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (forall y0 : real, (real_lt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term21 := (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0)))).
Definition term39 (x0 : real) := real_gt (sqrt x0) (real_of_num (NUMERAL 0)).
Definition term25 (x0 : real) := fun y0 : real => (real_gt y0 x0) = (real_lt x0 y0).
Definition term1 := fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term30 := fun y0 : real => forall y1 : real, (real_lt y0 y1) = (real_gt y1 y0).
Definition term29 := fun y0 : real => forall y1 : real, (real_gt y1 y0) = (real_lt y0 y1).
Definition term36 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) = (real_gt y1 y0)) x0.
Definition term20 := forall y0 : real, (real_lt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term12 := forall y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 := forall y0 : real, (y0 = (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL 0))).
Definition term15 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term41 (x0 : real) := @eq real (real_sgn x0).
Definition term42 (x0 : real) := @eq Prop (real_lt (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term44 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term34 (x0 : real) := real_sgn (sqrt x0).
Definition term17 := fun y0 : real => ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0))).
Definition term35 (x0 : real) := (fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) = ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term7 := real_of_num (NUMERAL (BIT1 0)).
Definition term19 := forall y0 : real, ((real_sgn y0) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt y0 (real_of_num (NUMERAL 0))).
Definition term11 := forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt y0 (real_of_num (NUMERAL 0))).
Definition term3 := forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term33 (x0 : real) := (fun y0 : real => (real_sgn (sqrt y0)) = (real_sgn y0)) x0.
Definition term38 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (sqrt x0).
