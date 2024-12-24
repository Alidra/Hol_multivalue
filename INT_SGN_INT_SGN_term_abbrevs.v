Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) := real_sgn (real_of_int x0).
Definition term7 (x0 : int) := @eq real (real_of_int (int_sgn (int_sgn x0))).
Definition term6 (x0 : int) := @eq real (real_sgn (real_sgn (real_of_int x0))).
Definition term0 (x0 : int) := (fun y0 : real => (real_sgn (real_sgn y0)) = (real_sgn y0)) (real_of_int x0).
Definition term5 (x0 : int) := real_of_int (int_sgn (int_sgn x0)).
Definition term8 (x0 : int) := int_sgn (int_sgn x0).
Definition term3 (x0 : int) := real_of_int (int_sgn x0).
Definition term9 := forall y0 : int, (int_sgn (int_sgn y0)) = (int_sgn y0).
Definition term1 (x0 : int) := real_sgn (real_sgn (real_of_int x0)).
Definition term4 (x0 : int) := real_sgn (real_of_int (int_sgn x0)).
