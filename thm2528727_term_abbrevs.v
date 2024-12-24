Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) (x1 : int) (x2 : int) := rem (rem x0 (int_mul x2 x1)) x2.
Definition term2 (x0 : int) (x1 : int) (x2 : int) := @eq2 int (rem x1 (int_mul x2 x0)) x1 (int_mod x2).
Definition term0 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
Definition term3 (x0 : int) (x1 : int) (x2 : int) := rem x0 (int_mul x1 x2).
