Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := (fun y0 : int => fun y1 : int => int_of_real (real_sub (real_of_int y0) (real_of_int y1))) x0.
Definition term0 := fun y0 : int => fun y1 : int => int_of_real (real_sub (real_of_int y0) (real_of_int y1)).
Definition term7 (x0 : int) := (fun y0 : int => forall y1 : int, (int_sub y0 y1) = (int_of_real (real_sub (real_of_int y0) (real_of_int y1)))) x0.
Definition term5 (x0 : int) := forall y0 : int, (int_sub x0 y0) = (int_of_real (real_sub (real_of_int x0) (real_of_int y0))).
Definition term4 (x0 : int) (x1 : int) := int_of_real (real_sub (real_of_int x0) (real_of_int x1)).
Definition term6 := forall y0 : int, forall y1 : int, (int_sub y0 y1) = (int_of_real (real_sub (real_of_int y0) (real_of_int y1))).
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => int_of_real (real_sub (real_of_int x0) (real_of_int y0))) x1.
Definition term2 (x0 : int) := fun y0 : int => int_of_real (real_sub (real_of_int x0) (real_of_int y0)).
Definition term8 (x0 : int) (x1 : int) := (fun y0 : int => (int_sub x0 y0) = (int_of_real (real_sub (real_of_int x0) (real_of_int y0)))) x1.
