Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := forall y0 : int, (real_add (real_of_int x0) (real_of_int y0)) = (real_of_int (int_add x0 y0)).
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, (real_add (real_of_int y0) (real_of_int y1)) = (real_of_int (int_add y0 y1))) x0.
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => (real_add (real_of_int x0) (real_of_int y0)) = (real_of_int (int_add x0 y0))) x1.
