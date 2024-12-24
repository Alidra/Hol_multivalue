Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : Prop) (x1 : int) (x2 : int) := real_of_int (@COND int x0 x1 x2).
Definition term1 (x0 : Prop) (x1 : int) (x2 : int) := @COND real x0 (real_of_int x1) (real_of_int x2).
