Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : int) (x2 : int) := @eq2 int (rem x0 (int_mul x1 x2)) x0 (int_mod (int_mul x1 x2)).
Definition term2 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => @eq2 int (rem x0 y0) x0 (int_mod y0)) (int_mul x1 x2).
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) x0.
Definition term1 (x0 : int) := forall y0 : int, @eq2 int (rem x0 y0) x0 (int_mod y0).
