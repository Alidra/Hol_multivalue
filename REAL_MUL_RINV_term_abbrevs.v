Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term14 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : real) := @eq real (real_mul (real_inv x0) x0).
Definition term18 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term16 := fun y0 : real => True.
Definition term13 := fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term11 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term3 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term10 (x0 : real) := imp (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term17 := forall y0 : real, True.
Definition term19 (x0 : Prop) := forall y0 : real, x0.
Definition term0 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term1 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term7 (x0 : real) := @eq real (real_mul x0 (real_inv x0)).
Definition term5 (x0 : real) := real_mul x0 (real_inv x0).
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term9 := real_of_num (NUMERAL (BIT1 0)).
Definition term6 (x0 : real) := real_mul (real_inv x0) x0.
Definition term12 := fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0))).
