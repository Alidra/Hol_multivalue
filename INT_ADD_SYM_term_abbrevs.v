Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : int) (x1 : int) := @eq real (real_add (real_of_int x0) (real_of_int x1)).
Definition term4 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) (real_of_int x0).
Definition term3 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term6 (x0 : int) (x1 : int) := @eq real (real_of_int (int_add x0 x1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_add (real_of_int x0) y0) = (real_add y0 (real_of_int x0))) (real_of_int x1).
Definition term7 (x0 : int) := forall y0 : int, (int_add x0 y0) = (int_add y0 x0).
Definition term8 := forall y0 : int, forall y1 : int, (int_add y0 y1) = (int_add y1 y0).
Definition term1 (x0 : int) := forall y0 : real, (real_add (real_of_int x0) y0) = (real_add y0 (real_of_int x0)).
