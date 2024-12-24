Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) (x1 : int) := @eq real (real_add (real_of_int x0) (real_of_int x1)).
Definition term1 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term0 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term3 (x0 : int) (x1 : int) := @eq real (real_of_int (int_add x0 x1)).
