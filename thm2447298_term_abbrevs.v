Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) (x1 : int) := exists y0 : int, x0 = (int_mul x1 y0).
Definition term0 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides y0 x0) = (exists y1 : int, x0 = (int_mul y0 y1))) x1.
