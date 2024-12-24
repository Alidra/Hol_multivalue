Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : int) (x1 : int) := real_mul (real_of_int (int_abs x0)) (real_of_int (int_abs x1)).
Definition term5 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term3 (x0 : int) (x1 : int) := real_abs (real_mul (real_of_int x0) (real_of_int x1)).
Definition term10 (x0 : int) (x1 : int) := real_of_int (int_abs (int_mul x0 x1)).
Definition term9 (x0 : int) := real_of_int (int_abs x0).
Definition term19 (x0 : int) := forall y0 : int, (int_abs (int_mul x0 y0)) = (int_mul (int_abs x0) (int_abs y0)).
Definition term18 (x0 : int) (x1 : int) := int_mul (int_abs x0) (int_abs x1).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1))) (real_of_int x0).
Definition term17 (x0 : int) (x1 : int) := int_abs (int_mul x0 x1).
Definition term14 (x0 : int) := real_mul (real_of_int (int_abs x0)).
Definition term20 := forall y0 : int, forall y1 : int, (int_abs (int_mul y0 y1)) = (int_mul (int_abs y0) (int_abs y1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_abs (real_mul (real_of_int x0) y0)) = (real_mul (real_abs (real_of_int x0)) (real_abs y0))) (real_of_int x1).
Definition term11 (x0 : int) (x1 : int) := @eq real (real_abs (real_mul (real_of_int x0) (real_of_int x1))).
Definition term7 (x0 : int) (x1 : int) := real_abs (real_of_int (int_mul x0 x1)).
Definition term12 (x0 : int) (x1 : int) := @eq real (real_of_int (int_abs (int_mul x0 x1))).
Definition term13 (x0 : int) := real_mul (real_abs (real_of_int x0)).
Definition term1 (x0 : int) := forall y0 : real, (real_abs (real_mul (real_of_int x0) y0)) = (real_mul (real_abs (real_of_int x0)) (real_abs y0)).
Definition term6 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term16 (x0 : int) (x1 : int) := real_of_int (int_mul (int_abs x0) (int_abs x1)).
Definition term8 (x0 : int) := real_abs (real_of_int x0).
Definition term4 (x0 : int) (x1 : int) := real_mul (real_abs (real_of_int x0)) (real_abs (real_of_int x1)).
