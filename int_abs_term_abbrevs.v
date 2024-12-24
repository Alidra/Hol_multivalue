Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := (fun y0 : int => int_of_real (real_abs (real_of_int y0))) x0.
Definition term3 := forall y0 : int, (int_abs y0) = (int_of_real (real_abs (real_of_int y0))).
Definition term2 (x0 : int) := int_of_real (real_abs (real_of_int x0)).
Definition term0 := fun y0 : int => int_of_real (real_abs (real_of_int y0)).
Definition term4 (x0 : int) := (fun y0 : int => (int_abs y0) = (int_of_real (real_abs (real_of_int y0)))) x0.
