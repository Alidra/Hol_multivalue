Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1.
Definition term0 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term36 (x0 : real) := @eq real (real_inv (real_neg x0)).
Definition term9 (x0 : real) := real_neg (real_neg x0).
Definition term39 (x0 : real) := ((real_mul (real_neg (real_inv x0)) (real_neg x0)) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv (real_neg x0)) = (real_neg (real_inv x0)).
Definition term31 := real_of_num (NUMERAL 0).
Definition term47 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term42 (x0 : real) := real_mul (real_inv x0) (real_neg x0).
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1.
Definition term46 (x0 : real) := @eq real (real_mul (real_inv x0) x0).
Definition term27 := (forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y1) = y0) -> forall y0 : real, forall y1 : real, ((real_mul y1 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term35 := real_inv (real_of_num (NUMERAL 0)).
Definition term41 (x0 : real) := real_neg (real_mul (real_inv x0) (real_neg x0)).
Definition term33 := real_neg (real_of_num (NUMERAL 0)).
Definition term30 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (real_of_num (NUMERAL 0))).
Definition term13 (x0 : real) (x1 : real) := real_mul x0 (real_neg x1).
Definition term34 (x0 : real) := real_inv (real_neg x0).
Definition term26 := forall y0 : real, forall y1 : real, ((real_mul y1 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term19 := forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y1) = y0.
Definition term29 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul y0 x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0) x1.
Definition term1 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term38 (x0 : real) := real_neg (real_inv x0).
Definition term2 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term14 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term3 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term37 := @eq real (real_of_num (NUMERAL 0)).
Definition term40 (x0 : real) := real_mul (real_neg (real_inv x0)) (real_neg x0).
Definition term8 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term11 (x0 : real) := forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term28 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y1 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1) x0.
Definition term20 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y1) = y0) x0.
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0.
Definition term10 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0.
Definition term18 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term25 (x0 : real) := forall y0 : real, ((real_mul y0 x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0.
Definition term7 := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term32 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term23 (x0 : real) (x1 : real) := ((real_mul x1 x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = x1.
Definition term16 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term6 (x0 : real) := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term21 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = x0.
Definition term45 (x0 : real) := @eq real (real_mul (real_neg (real_inv x0)) (real_neg x0)).
Definition term43 (x0 : real) := real_neg (real_mul (real_inv x0) x0).
Definition term5 := real_of_num (NUMERAL (BIT1 0)).
Definition term22 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = x0) x1.
Definition term48 := forall y0 : real, (real_inv (real_neg y0)) = (real_neg (real_inv y0)).
Definition term4 (x0 : real) := real_mul (real_inv x0) x0.
Definition term24 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y1) = y0) -> (real_inv x0) = x1.
Definition term44 (x0 : real) := real_neg (real_neg (real_mul (real_inv x0) x0)).
