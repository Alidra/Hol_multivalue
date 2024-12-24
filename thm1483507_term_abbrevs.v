Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term0 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
