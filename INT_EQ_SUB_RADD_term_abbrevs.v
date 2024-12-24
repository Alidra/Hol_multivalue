Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term5 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => ((real_sub (real_of_int x0) (real_of_int x1)) = y0) = ((real_of_int x0) = (real_add y0 (real_of_int x1)))) (real_of_int x2).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, ((real_sub (real_of_int x0) y0) = y1) = ((real_of_int x0) = (real_add y1 y0))) (real_of_int x1).
Definition term8 (x0 : int) (x1 : int) := @eq real (real_sub (real_of_int x0) (real_of_int x1)).
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, ((real_sub (real_of_int x0) y0) = y1) = ((real_of_int x0) = (real_add y1 y0)).
Definition term12 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_sub y0 y1) = y2) = (y0 = (real_add y2 y1))) (real_of_int x0).
Definition term10 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((real_sub (real_of_int x0) (real_of_int x1)) = (real_of_int x2)).
Definition term6 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term14 (x0 : int) (x1 : int) := forall y0 : int, ((int_sub x0 x1) = y0) = (x0 = (int_add y0 x1)).
Definition term16 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_sub y0 y1) = y2) = (y0 = (int_add y2 y1)).
Definition term15 (x0 : int) := forall y0 : int, forall y1 : int, ((int_sub x0 y0) = y1) = (x0 = (int_add y1 y0)).
Definition term11 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((int_sub x0 x1) = x2).
Definition term13 (x0 : int) := @eq real (real_of_int x0).
Definition term9 (x0 : int) (x1 : int) := @eq real (real_of_int (int_sub x0 x1)).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, ((real_sub (real_of_int x0) (real_of_int x1)) = y0) = ((real_of_int x0) = (real_add y0 (real_of_int x1))).
