Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_div y0 y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term1 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_inv x0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term10 (x0 : real) := imp (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term0 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul y0 (real_inv y0)) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term7 (x0 : real) := @eq real (real_div x0 x0).
Definition term8 (x0 : real) := @eq real (real_mul x0 (real_inv x0)).
Definition term6 (x0 : real) := real_mul x0 (real_inv x0).
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term11 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_div x0 x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term3 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term9 := real_of_num (NUMERAL (BIT1 0)).
Definition term5 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
