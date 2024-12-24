Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term10 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term8 (x0 : int) (x1 : int) := real_sub (real_abs (real_of_int x0)) (real_abs (real_of_int x1)).
Definition term7 (x0 : int) := real_sub (real_of_int (int_abs x0)).
Definition term17 (x0 : int) (x1 : int) := real_of_int (int_abs (int_sub x0 x1)).
Definition term15 (x0 : int) (x1 : int) := real_abs (real_sub (real_of_int x0) (real_of_int x1)).
Definition term12 (x0 : int) (x1 : int) := real_of_int (int_sub (int_abs x0) (int_abs x1)).
Definition term14 (x0 : int) (x1 : int) := real_le (real_of_int (int_sub (int_abs x0) (int_abs x1))).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => real_le (real_sub (real_abs (real_of_int x0)) (real_abs y0)) (real_abs (real_sub (real_of_int x0) y0))) (real_of_int x1).
Definition term23 (x0 : int) := forall y0 : int, int_le (int_sub (int_abs x0) (int_abs y0)) (int_abs (int_sub x0 y0)).
Definition term16 (x0 : int) (x1 : int) := real_abs (real_of_int (int_sub x0 x1)).
Definition term5 (x0 : int) := real_of_int (int_abs x0).
Definition term1 (x0 : int) := forall y0 : real, real_le (real_sub (real_abs (real_of_int x0)) (real_abs y0)) (real_abs (real_sub (real_of_int x0) y0)).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, real_le (real_sub (real_abs y0) (real_abs y1)) (real_abs (real_sub y0 y1))) (real_of_int x0).
Definition term6 (x0 : int) := real_sub (real_abs (real_of_int x0)).
Definition term24 := forall y0 : int, forall y1 : int, int_le (int_sub (int_abs y0) (int_abs y1)) (int_abs (int_sub y0 y1)).
Definition term18 (x0 : int) (x1 : int) := real_le (real_of_int (int_sub (int_abs x0) (int_abs x1))) (real_of_int (int_abs (int_sub x0 x1))).
Definition term3 (x0 : int) (x1 : int) := real_le (real_sub (real_abs (real_of_int x0)) (real_abs (real_of_int x1))) (real_abs (real_sub (real_of_int x0) (real_of_int x1))).
Definition term19 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term20 (x0 : int) (x1 : int) := int_le (int_sub (int_abs x0) (int_abs x1)) (int_abs (int_sub x0 x1)).
Definition term13 (x0 : int) (x1 : int) := real_le (real_sub (real_abs (real_of_int x0)) (real_abs (real_of_int x1))).
Definition term9 (x0 : int) (x1 : int) := real_sub (real_of_int (int_abs x0)) (real_of_int (int_abs x1)).
Definition term4 (x0 : int) := real_abs (real_of_int x0).
Definition term22 (x0 : int) (x1 : int) := int_abs (int_sub x0 x1).
Definition term21 (x0 : int) (x1 : int) := int_sub (int_abs x0) (int_abs x1).
