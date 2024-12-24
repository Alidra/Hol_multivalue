Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) (x1 : int) (x2 : int) := int_mul (int_add x0 x1) x2.
Definition term0 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul x0 x2) (int_mul x1 x2).
