Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term14 := fun y0 : int => True.
Definition term7 (x0 : int) := (fun y0 : int => forall y1 : int, (int_ge y0 y1) = (real_ge (real_of_int y0) (real_of_int y1))) x0.
Definition term3 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le y0 y1) = (real_le (real_of_int y0) (real_of_int y1))) x0.
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_ge y0 x0) = (real_le x0 y0)) x1.
Definition term1 (x0 : real) := forall y0 : real, (real_ge y0 x0) = (real_le x0 y0).
Definition term13 (x0 : int) := fun y0 : int => (int_ge x0 y0) = (int_le y0 x0).
Definition term8 (x0 : int) := forall y0 : int, (int_ge x0 y0) = (real_ge (real_of_int x0) (real_of_int y0)).
Definition term4 (x0 : int) := forall y0 : int, (int_le x0 y0) = (real_le (real_of_int x0) (real_of_int y0)).
Definition term15 (x0 : int) := forall y0 : int, (int_ge x0 y0) = (int_le y0 x0).
Definition term18 (x0 : Prop) := forall y0 : int, x0.
Definition term10 (x0 : int) (x1 : int) := real_ge (real_of_int x0) (real_of_int x1).
Definition term20 := forall y0 : int, forall y1 : int, (int_ge y0 y1) = (int_le y1 y0).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_ge y1 y0) = (real_le y0 y1)) x0.
Definition term19 := fun y0 : int => forall y1 : int, (int_ge y0 y1) = (int_le y1 y0).
Definition term16 := forall y0 : int, True.
Definition term6 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term11 (x0 : int) (x1 : int) := @eq Prop (int_ge x0 x1).
Definition term12 (x0 : int) (x1 : int) := @eq Prop (real_le (real_of_int x0) (real_of_int x1)).
Definition term5 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) = (real_le (real_of_int x0) (real_of_int y0))) x1.
Definition term9 (x0 : int) (x1 : int) := (fun y0 : int => (int_ge x0 y0) = (real_ge (real_of_int x0) (real_of_int y0))) x1.
