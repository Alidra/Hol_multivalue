Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x1 (real_mul x0 y0)) = (real_mul x0 (real_mul x1 y0)).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term10 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term17 (x0 : int) (x1 : int) (x2 : int) := int_mul x0 (int_mul x1 x2).
Definition term6 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_mul (real_of_int x0) y1)) = (real_mul (real_of_int x0) (real_mul y0 y1))) (real_of_int x1).
Definition term5 (x0 : int) := forall y0 : real, forall y1 : real, (real_mul y0 (real_mul (real_of_int x0) y1)) = (real_mul (real_of_int x0) (real_mul y0 y1)).
Definition term3 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y1 (real_mul y0 y2)) = (real_mul y0 (real_mul y1 y2)).
Definition term2 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul y0 (real_mul x0 y1)) = (real_mul x0 (real_mul y0 y1)).
Definition term7 (x0 : int) (x1 : int) := forall y0 : real, (real_mul (real_of_int x1) (real_mul (real_of_int x0) y0)) = (real_mul (real_of_int x0) (real_mul (real_of_int x1) y0)).
Definition term4 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y1 (real_mul y0 y2)) = (real_mul y0 (real_mul y1 y2))) (real_of_int x0).
Definition term9 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x0) (real_mul (real_of_int x1) (real_of_int x2)).
Definition term8 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => (real_mul (real_of_int x1) (real_mul (real_of_int x0) y0)) = (real_mul (real_of_int x0) (real_mul (real_of_int x1) y0))) (real_of_int x2).
Definition term16 (x0 : int) (x1 : int) (x2 : int) := @eq real (real_of_int (int_mul x0 (int_mul x1 x2))).
Definition term14 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_mul x0 (int_mul x1 x2)).
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term12 (x0 : int) := real_mul (real_of_int x0).
Definition term13 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x0) (real_of_int (int_mul x1 x2)).
Definition term15 (x0 : int) (x1 : int) (x2 : int) := @eq real (real_mul (real_of_int x0) (real_mul (real_of_int x1) (real_of_int x2))).