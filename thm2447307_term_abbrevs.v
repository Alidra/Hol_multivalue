Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = (exists y1 : int, (int_sub x0 x1) = (int_mul y0 y1))) x2.
Definition term2 (x0 : int) (x1 : int) (x2 : int) := exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0).
Definition term1 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
