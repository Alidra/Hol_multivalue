Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 := fun y0 : int => exists y1 : nat, ((real_of_int y0) = (real_of_num y1)) \/ ((real_of_int y0) = (real_neg (real_of_num y1))).
Definition term12 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term9 := fun y0 : int => True.
Definition term3 (x0 : real) := real_of_int (int_of_real x0).
Definition term5 (x0 : int) := int_of_real (real_of_int x0).
Definition term1 (x0 : int) := exists y0 : nat, ((real_of_int x0) = (real_of_num y0)) \/ ((real_of_int x0) = (real_neg (real_of_num y0))).
Definition term2 (x0 : int) := integer (real_of_int x0).
Definition term4 (x0 : int) := real_of_int (int_of_real (real_of_int x0)).
Definition term6 (x0 : int) := @eq real (real_of_int (int_of_real (real_of_int x0))).
Definition term13 (x0 : Prop) := forall y0 : int, x0.
Definition term11 := forall y0 : int, True.
Definition term0 (x0 : real) := exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))).
Definition term10 := forall y0 : int, exists y1 : nat, ((real_of_int y0) = (real_of_num y1)) \/ ((real_of_int y0) = (real_neg (real_of_num y1))).
Definition term7 (x0 : int) := @eq real (real_of_int x0).
