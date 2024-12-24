Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : int) (x2 : int) := @eq2 int (rem x1 (int_mul x2 x0)) x1 (int_mod x2).
