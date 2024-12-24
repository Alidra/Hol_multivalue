Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := forall y0 : real, (real_le (real_of_int x0) y0) \/ (real_le y0 (real_of_int x0)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_le (real_of_int x0) y0) \/ (real_le y0 (real_of_int x0))) (real_of_int x1).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) (real_of_int x0).
Definition term9 := forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0).
Definition term7 (x0 : int) (x1 : int) := (int_le x1 x0) \/ (int_le x0 x1).
Definition term3 (x0 : int) (x1 : int) := (real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_of_int x0) (real_of_int x1)).
Definition term6 (x0 : int) (x1 : int) := or (int_le x0 x1).
Definition term8 (x0 : int) := forall y0 : int, (int_le x0 y0) \/ (int_le y0 x0).
Definition term4 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term5 (x0 : int) (x1 : int) := or (real_le (real_of_int x0) (real_of_int x1)).
