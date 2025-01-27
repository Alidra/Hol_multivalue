Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0))) x1.
Definition term39 (x0 : real) := (fun y0 : real => (real_abs y0) = (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_inv x0)).
Definition term23 := real_of_num (NUMERAL 0).
Definition term28 := real_abs (real_of_num (NUMERAL 0)).
Definition term21 := (forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1) -> forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term35 (x0 : real) := @eq real (real_mul (real_abs x0) (real_abs (real_inv x0))).
Definition term4 (x0 : real) := fun y0 : real => (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term1 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term29 := real_inv (real_of_num (NUMERAL 0)).
Definition term22 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (real_of_num (NUMERAL 0))).
Definition term14 := forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term11 := forall y0 : real, forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1)).
Definition term10 := forall y0 : real, forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1)).
Definition term46 := forall y0 : real, (real_abs (real_inv y0)) = (real_inv (real_abs y0)).
Definition term17 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0) x1.
Definition term0 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term27 (x0 : real) := real_inv (real_abs x0).
Definition term25 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term32 (x0 : real) := ((real_mul (real_abs x0) (real_abs (real_inv x0))) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv (real_abs x0)) = (real_abs (real_inv x0)).
Definition term8 := fun y0 : real => forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1)).
Definition term31 := @eq real (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) := real_mul (real_abs x0) (real_abs (real_inv x0)).
Definition term37 (x0 : real) := real_mul x0 (real_inv x0).
Definition term2 (x0 : real) (x1 : real) := real_abs (real_mul x0 x1).
Definition term34 (x0 : real) := real_abs (real_mul x0 (real_inv x0)).
Definition term38 := fun y0 : real => (real_abs y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1) x0.
Definition term12 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1))) x0.
Definition term41 := real_abs (real_of_num (NUMERAL (BIT1 0))).
Definition term5 (x0 : real) := fun y0 : real => (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0)).
Definition term26 (x0 : real) := real_abs (real_inv x0).
Definition term16 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0.
Definition term24 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term18 (x0 : real) (x1 : real) := ((real_mul x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = x1.
Definition term7 (x0 : real) := forall y0 : real, (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0)).
Definition term30 (x0 : real) := @eq real (real_inv (real_abs x0)).
Definition term42 (x0 : real) := @eq Prop ((fun y0 : real => (real_abs y0) = (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_inv x0))).
Definition term44 := @eq real (real_abs (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 (x0 : real) := forall y0 : real, (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term19 := real_of_num (NUMERAL (BIT1 0)).
Definition term40 := (fun y0 : real => (real_abs y0) = (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term36 (x0 : real) := @eq real (real_abs (real_mul x0 (real_inv x0))).
Definition term3 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs x1).
Definition term45 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term20 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1) -> (real_inv x0) = x1.
Definition term43 (x0 : real) := @eq Prop ((real_abs (real_mul x0 (real_inv x0))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term9 := fun y0 : real => forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1)).
