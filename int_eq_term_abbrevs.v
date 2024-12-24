Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : int) (x1 : int) := (x0 = x1) -> (real_of_int x0) = (real_of_int x1).
Definition term5 (x0 : int) (x1 : int) := ((int_of_real (real_of_int x0)) = (int_of_real (real_of_int x1))) -> x0 = x1.
Definition term1 (x0 : int) := int_of_real (real_of_int x0).
Definition term10 (x0 : int) := forall y0 : int, (x0 = y0) = ((real_of_int x0) = (real_of_int y0)).
Definition term3 (x0 : int) (x1 : int) := imp ((int_of_real (real_of_int x0)) = (int_of_real (real_of_int x1))).
Definition term7 (x0 : int) (x1 : int) := ((real_of_int x0) = (real_of_int x1)) -> x0 = x1.
Definition term2 (x0 : int) := @eq int (int_of_real (real_of_int x0)).
Definition term11 := forall y0 : int, forall y1 : int, (y0 = y1) = ((real_of_int y0) = (real_of_int y1)).
Definition term4 (x0 : int) (x1 : int) := imp (x0 = x1).
Definition term9 (x0 : int) (x1 : int) := ((x0 = x1) -> (real_of_int x0) = (real_of_int x1)) /\ (((real_of_int x0) = (real_of_int x1)) -> x0 = x1).
Definition term6 (x0 : int) (x1 : int) := (x0 = x1) -> x0 = x1.
Definition term0 (x0 : int) := @eq real (real_of_int x0).
