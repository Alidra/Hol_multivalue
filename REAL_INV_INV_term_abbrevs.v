Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term16 := real_of_num (NUMERAL 0).
Definition term23 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term22 (x0 : real) := ((real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv (real_inv x0)) = x0.
Definition term14 := (forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1) -> forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term18 := real_inv (real_of_num (NUMERAL 0)).
Definition term15 (x0 : real) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (real_of_num (NUMERAL 0))).
Definition term8 := forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1.
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0) x1.
Definition term1 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term24 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term2 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term3 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term20 (x0 : real) := @eq real (real_inv (real_inv x0)).
Definition term21 := @eq real (real_of_num (NUMERAL 0)).
Definition term19 (x0 : real) := real_inv (real_inv x0).
Definition term9 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1) x0.
Definition term10 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = y0.
Definition term7 := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term17 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term12 (x0 : real) (x1 : real) := ((real_mul x0 x1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv x0) = x1.
Definition term6 (x0 : real) := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term5 := real_of_num (NUMERAL (BIT1 0)).
Definition term4 (x0 : real) := real_mul (real_inv x0) x0.
Definition term13 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y0) = y1) -> (real_inv x0) = x1.
