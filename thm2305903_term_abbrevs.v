Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term0 (x0 : real) := forall y0 : real, (real_mul y0 x0) = (real_mul x0 y0).
Definition term1 := forall y0 : real, forall y1 : real, (real_mul y1 y0) = (real_mul y0 y1).
Definition term2 (x0 : int) := (fun y0 : real => forall y1 : real, (real_mul y1 y0) = (real_mul y0 y1)) (real_of_int x0).
Definition term3 (x0 : int) := forall y0 : real, (real_mul y0 (real_of_int x0)) = (real_mul (real_of_int x0) y0).
Definition term4 (x0 : int) (x1 : int) := (fun y0 : real => (real_mul y0 (real_of_int x0)) = (real_mul (real_of_int x0) y0)) (real_of_int x1).
