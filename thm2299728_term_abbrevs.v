Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 := fun y0 : int => forall y1 : int, (int_ge y0 y1) = (real_ge (real_of_int y0) (real_of_int y1)).
Definition term2 (x0 : int) := fun y0 : int => (real_ge (real_of_int x0) (real_of_int y0)) = (int_ge x0 y0).
Definition term1 (x0 : int) := fun y0 : int => (int_ge x0 y0) = (real_ge (real_of_int x0) (real_of_int y0)).
Definition term4 (x0 : int) := forall y0 : int, (real_ge (real_of_int x0) (real_of_int y0)) = (int_ge x0 y0).
Definition term3 (x0 : int) := forall y0 : int, (int_ge x0 y0) = (real_ge (real_of_int x0) (real_of_int y0)).
Definition term0 (x0 : int) (x1 : int) := real_ge (real_of_int x0) (real_of_int x1).
Definition term8 := forall y0 : int, forall y1 : int, (real_ge (real_of_int y0) (real_of_int y1)) = (int_ge y0 y1).
Definition term7 := forall y0 : int, forall y1 : int, (int_ge y0 y1) = (real_ge (real_of_int y0) (real_of_int y1)).
Definition term6 := fun y0 : int => forall y1 : int, (real_ge (real_of_int y0) (real_of_int y1)) = (int_ge y0 y1).
