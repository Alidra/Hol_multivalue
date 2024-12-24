Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0))) x1.
Definition term16 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul x0 (real_mul (real_inv x1) (real_mul x2 (real_inv x3))).
Definition term5 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term22 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_div (real_mul x0 x1) (real_mul x2 x3).
Definition term19 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul x0 (real_mul x1 (real_mul (real_inv x2) (real_inv x3))).
Definition term12 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_div x0 x1) (real_div x2 x3).
Definition term24 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul x0 (real_mul x1 (real_inv (real_mul x2 x3))).
Definition term13 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_mul x0 (real_inv x1)) (real_mul x2 (real_inv x3)).
Definition term25 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_inv (real_mul x1 x2)).
Definition term23 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_mul x0 x1) (real_inv (real_mul x2 x3)).
Definition term20 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_mul (real_div x0 x1) (real_div x2 x3)).
Definition term10 (x0 : real) (x1 : real) := real_mul (real_div x0 x1).
Definition term17 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_inv x0) (real_mul x1 (real_inv x2)).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul (real_inv x1) (real_inv x2)).
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, (real_inv (real_mul y0 y1)) = (real_mul (real_inv y0) (real_inv y1))) x0.
Definition term7 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term11 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv x1)).
Definition term4 (x0 : real) (x1 : real) := real_inv (real_mul x0 x1).
Definition term2 (x0 : real) := forall y0 : real, (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0)).
Definition term14 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term9 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := ((real_mul (real_mul x1 x0) x2) = (real_mul x1 (real_mul x0 x2))) /\ ((real_mul x1 (real_mul x0 x2)) = (real_mul x0 (real_mul x1 x2))).
Definition term21 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_mul x0 (real_mul x1 (real_mul (real_inv x2) (real_inv x3)))).
