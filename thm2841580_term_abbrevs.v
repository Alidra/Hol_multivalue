Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term0 (x0 : int) (x1 : int) := (fun y0 : int => (real_of_int (int_mul x0 y0)) = (real_mul (real_of_int x0) (real_of_int y0))) x1.