Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : int) := @eq real (real_of_int (int_neg (int_neg x0))).
Definition term1 (x0 : int) := real_neg (real_neg (real_of_int x0)).
Definition term4 (x0 : int) := real_neg (real_of_int (int_neg x0)).
Definition term6 (x0 : int) := @eq real (real_neg (real_neg (real_of_int x0))).
Definition term9 := forall y0 : int, (int_neg (int_neg y0)) = y0.
Definition term8 (x0 : int) := int_neg (int_neg x0).
Definition term2 (x0 : int) := real_neg (real_of_int x0).
Definition term0 (x0 : int) := (fun y0 : real => (real_neg (real_neg y0)) = y0) (real_of_int x0).
Definition term3 (x0 : int) := real_of_int (int_neg x0).
Definition term5 (x0 : int) := real_of_int (int_neg (int_neg x0)).
