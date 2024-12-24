Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term10 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term21 (x0 : int) := forall y0 : int, (int_sub (int_neg x0) y0) = (int_neg (int_add x0 y0)).
Definition term8 (x0 : int) := real_sub (real_of_int (int_neg x0)).
Definition term14 (x0 : int) (x1 : int) := @eq real (real_of_int (int_sub (int_neg x0) x1)).
Definition term18 (x0 : int) (x1 : int) := real_of_int (int_neg (int_add x0 x1)).
Definition term17 (x0 : int) (x1 : int) := real_neg (real_of_int (int_add x0 x1)).
Definition term20 (x0 : int) (x1 : int) := int_neg (int_add x0 x1).
Definition term16 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term19 (x0 : int) (x1 : int) := int_sub (int_neg x0) x1.
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_sub (real_neg y0) y1) = (real_neg (real_add y0 y1))) (real_of_int x0).
Definition term15 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term7 (x0 : int) := real_sub (real_neg (real_of_int x0)).
Definition term12 (x0 : int) (x1 : int) := real_of_int (int_sub (int_neg x0) x1).
Definition term22 := forall y0 : int, forall y1 : int, (int_sub (int_neg y0) y1) = (int_neg (int_add y0 y1)).
Definition term4 (x0 : int) (x1 : int) := real_neg (real_add (real_of_int x0) (real_of_int x1)).
Definition term13 (x0 : int) (x1 : int) := @eq real (real_sub (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term1 (x0 : int) := forall y0 : real, (real_sub (real_neg (real_of_int x0)) y0) = (real_neg (real_add (real_of_int x0) y0)).
Definition term5 (x0 : int) := real_neg (real_of_int x0).
Definition term6 (x0 : int) := real_of_int (int_neg x0).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_sub (real_neg (real_of_int x0)) y0) = (real_neg (real_add (real_of_int x0) y0))) (real_of_int x1).
Definition term9 (x0 : int) (x1 : int) := real_sub (real_of_int (int_neg x0)) (real_of_int x1).
Definition term3 (x0 : int) (x1 : int) := real_sub (real_neg (real_of_int x0)) (real_of_int x1).
