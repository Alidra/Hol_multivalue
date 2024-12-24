Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := forall y0 : int, int_le y0 y0.
Definition term2 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := real_le (real_of_int x0) (real_of_int x0).
Definition term0 (x0 : int) := (fun y0 : real => real_le y0 y0) (real_of_int x0).
