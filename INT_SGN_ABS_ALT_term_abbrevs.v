Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) := real_sgn (real_of_int x0).
Definition term15 := forall y0 : int, (int_mul (int_sgn y0) y0) = (int_abs y0).
Definition term8 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := real_mul (real_sgn (real_of_int x0)) (real_of_int x0).
Definition term6 (x0 : int) := real_mul (real_of_int (int_sgn x0)).
Definition term5 (x0 : int) := real_mul (real_sgn (real_of_int x0)).
Definition term14 (x0 : int) := int_mul (int_sgn x0) x0.
Definition term13 (x0 : int) := real_of_int (int_abs x0).
Definition term10 (x0 : int) := real_of_int (int_mul (int_sgn x0) x0).
Definition term7 (x0 : int) := real_mul (real_of_int (int_sgn x0)) (real_of_int x0).
Definition term4 (x0 : int) := real_of_int (int_sgn x0).
Definition term12 (x0 : int) := @eq real (real_of_int (int_mul (int_sgn x0) x0)).
Definition term11 (x0 : int) := @eq real (real_mul (real_sgn (real_of_int x0)) (real_of_int x0)).
Definition term0 (x0 : int) := (fun y0 : real => (real_mul (real_sgn y0) y0) = (real_abs y0)) (real_of_int x0).
Definition term9 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term2 (x0 : int) := real_abs (real_of_int x0).