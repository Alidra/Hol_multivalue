Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_add x0 x1)) (real_of_int x2).
Definition term13 (x0 : int) (x1 : int) (x2 : int) := @eq real (real_of_int (int_add x0 (int_add x1 x2))).
Definition term10 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int x0) (real_of_int (int_add x1 x2)).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => forall y1 : real, (real_add (real_of_int x0) (real_add y0 y1)) = (real_add (real_add (real_of_int x0) y0) y1)) (real_of_int x1).
Definition term17 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_add (int_add x0 x1) x2).
Definition term1 (x0 : int) := forall y0 : real, forall y1 : real, (real_add (real_of_int x0) (real_add y0 y1)) = (real_add (real_add (real_of_int x0) y0) y1).
Definition term8 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term14 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)).
Definition term9 (x0 : int) := real_add (real_of_int x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) (real_of_int x0).
Definition term7 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term3 (x0 : int) (x1 : int) := forall y0 : real, (real_add (real_of_int x0) (real_add (real_of_int x1) y0)) = (real_add (real_add (real_of_int x0) (real_of_int x1)) y0).
Definition term11 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_add x0 (int_add x1 x2)).
Definition term20 (x0 : int) (x1 : int) := forall y0 : int, (int_add x0 (int_add x1 y0)) = (int_add (int_add x0 x1) y0).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : real => (real_add (real_of_int x0) (real_add (real_of_int x1) y0)) = (real_add (real_add (real_of_int x0) (real_of_int x1)) y0)) (real_of_int x2).
Definition term19 (x0 : int) (x1 : int) (x2 : int) := int_add (int_add x0 x1) x2.
Definition term22 := forall y0 : int, forall y1 : int, forall y2 : int, (int_add y0 (int_add y1 y2)) = (int_add (int_add y0 y1) y2).
Definition term21 (x0 : int) := forall y0 : int, forall y1 : int, (int_add x0 (int_add y0 y1)) = (int_add (int_add x0 y0) y1).
Definition term12 (x0 : int) (x1 : int) (x2 : int) := @eq real (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))).
Definition term6 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_int x2).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := int_add x0 (int_add x1 x2).
Definition term15 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)).