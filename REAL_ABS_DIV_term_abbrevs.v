Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : real) (x1 : real) := real_abs (real_div x0 x1).
Definition term20 (x0 : real) := fun y0 : real => (real_abs (real_div x0 y0)) = (real_div (real_abs x0) (real_abs y0)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0))) x1.
Definition term16 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_inv (real_abs x1)).
Definition term15 (x0 : real) := real_mul (real_abs x0).
Definition term24 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term21 := fun y0 : real => True.
Definition term23 := forall y0 : real, True.
Definition term25 (x0 : Prop) := forall y0 : real, x0.
Definition term10 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term27 := forall y0 : real, forall y1 : real, (real_abs (real_div y0 y1)) = (real_div (real_abs y0) (real_abs y1)).
Definition term7 (x0 : real) := real_inv (real_abs x0).
Definition term13 (x0 : real) (x1 : real) := real_abs (real_mul x0 (real_inv x1)).
Definition term26 := fun y0 : real => forall y1 : real, (real_abs (real_div y0 y1)) = (real_div (real_abs y0) (real_abs y1)).
Definition term18 (x0 : real) (x1 : real) := @eq real (real_mul (real_abs x0) (real_inv (real_abs x1))).
Definition term19 (x0 : real) (x1 : real) := real_div (real_abs x0) (real_abs x1).
Definition term14 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs (real_inv x1)).
Definition term3 (x0 : real) (x1 : real) := real_abs (real_mul x0 x1).
Definition term17 (x0 : real) (x1 : real) := @eq real (real_abs (real_div x0 x1)).
Definition term8 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1))) x0.
Definition term5 (x0 : real) := (fun y0 : real => (real_abs (real_inv y0)) = (real_inv (real_abs y0))) x0.
Definition term6 (x0 : real) := real_abs (real_inv x0).
Definition term9 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term22 (x0 : real) := forall y0 : real, (real_abs (real_div x0 y0)) = (real_div (real_abs x0) (real_abs y0)).
Definition term1 (x0 : real) := forall y0 : real, (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term4 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs x1).
Definition term11 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
