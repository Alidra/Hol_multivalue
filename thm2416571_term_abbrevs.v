Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : int) := int_mul (int_pow x1 x0) x1.
Definition term1 (x0 : int) (x1 : nat) := int_pow x0 (S x1).
