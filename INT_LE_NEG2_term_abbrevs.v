Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : int) := real_le (real_neg (real_of_int x0)) (real_neg (real_of_int x1)).
Definition term10 (x0 : int) (x1 : int) := int_le (int_neg x0) (int_neg x1).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_le (real_neg y0) (real_neg y1)) = (real_le y1 y0)) (real_of_int x0).
Definition term8 (x0 : int) := real_le (real_of_int (int_neg x0)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_le (real_neg (real_of_int x0)) (real_neg y0)) = (real_le y0 (real_of_int x0))) (real_of_int x1).
Definition term14 := forall y0 : int, forall y1 : int, (int_le (int_neg y0) (int_neg y1)) = (int_le y1 y0).
Definition term12 (x0 : int) (x1 : int) := @eq Prop (int_le (int_neg x0) (int_neg x1)).
Definition term5 (x0 : int) := real_neg (real_of_int x0).
Definition term4 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := forall y0 : real, (real_le (real_neg (real_of_int x0)) (real_neg y0)) = (real_le y0 (real_of_int x0)).
Definition term11 (x0 : int) (x1 : int) := @eq Prop (real_le (real_neg (real_of_int x0)) (real_neg (real_of_int x1))).
Definition term9 (x0 : int) (x1 : int) := real_le (real_of_int (int_neg x0)) (real_of_int (int_neg x1)).
Definition term6 (x0 : int) := real_of_int (int_neg x0).
Definition term13 (x0 : int) := forall y0 : int, (int_le (int_neg x0) (int_neg y0)) = (int_le y0 x0).
Definition term7 (x0 : int) := real_le (real_neg (real_of_int x0)).