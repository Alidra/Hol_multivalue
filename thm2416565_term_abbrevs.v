Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) (x1 : int) (x2 : int) := int_add (int_add x0 x1) x2.
Definition term0 (x0 : int) (x1 : int) (x2 : int) := int_add x0 (int_add x1 x2).
