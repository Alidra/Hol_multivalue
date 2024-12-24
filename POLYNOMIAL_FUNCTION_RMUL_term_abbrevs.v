Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term22 := fun y0 : real => True.
Definition term8 (x0 : real) (x1 : real -> real) (x2 : real) := real_mul x0 (x1 x2).
Definition term5 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term6 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term23 := forall y0 : real, True.
Definition term25 (x0 : Prop) := forall y0 : real, x0.
Definition term10 (x0 : real) (x1 : real -> real) := fun y0 : real => real_mul x0 (x1 y0).
Definition term2 (x0 : real -> real) (x1 : real) := (fun y0 : real => (polynomial_function x0) -> polynomial_function (fun y1 : real => real_mul y0 (x0 y1))) x1.
Definition term0 (x0 : real -> real) := (fun y0 : real -> real => forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul y1 (y0 y2))) x0.
Definition term7 (x0 : real -> real) (x1 : real) (x2 : real) := real_mul (x0 x1) x2.
Definition term26 := fun y0 : real -> real => True.
Definition term11 (x0 : real -> real) (x1 : real) := polynomial_function (fun y0 : real => real_mul (x0 y0) x1).
Definition term27 := forall y0 : real -> real, True.
Definition term17 (x0 : real -> real) := forall y0 : real, (polynomial_function x0) -> polynomial_function (fun y1 : real => real_mul (x0 y1) y0).
Definition term1 (x0 : real -> real) := forall y0 : real, (polynomial_function x0) -> polynomial_function (fun y1 : real => real_mul y0 (x0 y1)).
Definition term9 (x0 : real -> real) (x1 : real) := fun y0 : real => real_mul (x0 y0) x1.
Definition term4 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term16 (x0 : real -> real) := fun y0 : real => (polynomial_function x0) -> polynomial_function (fun y1 : real => real_mul y0 (x0 y1)).
Definition term15 (x0 : real -> real) := fun y0 : real => (polynomial_function x0) -> polynomial_function (fun y1 : real => real_mul (x0 y1) y0).
Definition term21 := forall y0 : real -> real, forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul y1 (y0 y2)).
Definition term20 := forall y0 : real -> real, forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul (y0 y2) y1).
Definition term14 (x0 : real -> real) (x1 : real) := (polynomial_function x0) -> polynomial_function (fun y0 : real => real_mul (x0 y0) x1).
Definition term19 := fun y0 : real -> real => forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul y1 (y0 y2)).
Definition term18 := fun y0 : real -> real => forall y1 : real, (polynomial_function y0) -> polynomial_function (fun y2 : real => real_mul (y0 y2) y1).
Definition term28 (x0 : Prop) := forall y0 : real -> real, x0.
Definition term3 (x0 : real) (x1 : real -> real) := (polynomial_function x1) -> polynomial_function (fun y0 : real => real_mul x0 (x1 y0)).
Definition term13 (x0 : real -> real) := imp (polynomial_function x0).
Definition term12 (x0 : real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_mul x0 (x1 y0)).
