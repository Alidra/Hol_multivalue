Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : int) (x1 : int) := or (int_lt x0 x1).
Definition term12 (x0 : int) := forall y0 : int, (~ (x0 = y0)) = ((int_lt x0 y0) \/ (int_lt y0 x0)).
Definition term3 (x0 : int) (x1 : int) := ~ ((real_of_int x0) = (real_of_int x1)).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (~ (y0 = y1)) = ((real_lt y0 y1) \/ (real_lt y1 y0))) (real_of_int x0).
Definition term4 (x0 : int) (x1 : int) := (real_lt (real_of_int x1) (real_of_int x0)) \/ (real_lt (real_of_int x0) (real_of_int x1)).
Definition term8 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := forall y0 : real, (~ ((real_of_int x0) = y0)) = ((real_lt (real_of_int x0) y0) \/ (real_lt y0 (real_of_int x0))).
Definition term13 := forall y0 : int, forall y1 : int, (~ (y0 = y1)) = ((int_lt y0 y1) \/ (int_lt y1 y0)).
Definition term11 (x0 : int) (x1 : int) := (int_lt x1 x0) \/ (int_lt x0 x1).
Definition term5 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term6 (x0 : int) (x1 : int) := @eq Prop (~ ((real_of_int x0) = (real_of_int x1))).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (~ ((real_of_int x0) = y0)) = ((real_lt (real_of_int x0) y0) \/ (real_lt y0 (real_of_int x0)))) (real_of_int x1).
Definition term9 (x0 : int) (x1 : int) := or (real_lt (real_of_int x0) (real_of_int x1)).
Definition term7 (x0 : int) (x1 : int) := @eq Prop (~ (x0 = x1)).
