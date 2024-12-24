Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := real_sgn (real_of_int x0).
Definition term2 := fun y0 : int => (real_of_int (int_sgn y0)) = (real_sgn (real_of_int y0)).
Definition term3 := fun y0 : int => (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0)).
Definition term5 := forall y0 : int, (real_sgn (real_of_int y0)) = (real_of_int (int_sgn y0)).
Definition term0 (x0 : int) := real_of_int (int_sgn x0).
Definition term4 := forall y0 : int, (real_of_int (int_sgn y0)) = (real_sgn (real_of_int y0)).
