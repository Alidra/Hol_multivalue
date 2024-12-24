Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : int) := real_sgn (real_of_int x0).
Definition term11 (x0 : int) (x1 : int) := and ((int_sgn x0) = (int_sgn x1)).
Definition term13 (x0 : int) := real_of_int (int_abs x0).
Definition term9 (x0 : int) := @eq real (real_of_int (int_sgn x0)).
Definition term16 (x0 : int) (x1 : int) := ((int_sgn x0) = (int_sgn x1)) /\ ((int_abs x0) = (int_abs x1)).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (y0 = y1) = (((real_sgn y0) = (real_sgn y1)) /\ ((real_abs y0) = (real_abs y1)))) (real_of_int x0).
Definition term14 (x0 : int) := @eq real (real_abs (real_of_int x0)).
Definition term17 (x0 : int) := forall y0 : int, (x0 = y0) = (((int_sgn x0) = (int_sgn y0)) /\ ((int_abs x0) = (int_abs y0))).
Definition term10 (x0 : int) (x1 : int) := and ((real_sgn (real_of_int x0)) = (real_sgn (real_of_int x1))).
Definition term18 := forall y0 : int, forall y1 : int, (y0 = y1) = (((int_sgn y0) = (int_sgn y1)) /\ ((int_abs y0) = (int_abs y1))).
Definition term7 (x0 : int) := real_of_int (int_sgn x0).
Definition term8 (x0 : int) := @eq real (real_sgn (real_of_int x0)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => ((real_of_int x0) = y0) = (((real_sgn (real_of_int x0)) = (real_sgn y0)) /\ ((real_abs (real_of_int x0)) = (real_abs y0)))) (real_of_int x1).
Definition term5 (x0 : int) (x1 : int) := @eq Prop (x0 = x1).
Definition term12 (x0 : int) := real_abs (real_of_int x0).
Definition term4 (x0 : int) (x1 : int) := @eq Prop ((real_of_int x0) = (real_of_int x1)).
Definition term1 (x0 : int) := forall y0 : real, ((real_of_int x0) = y0) = (((real_sgn (real_of_int x0)) = (real_sgn y0)) /\ ((real_abs (real_of_int x0)) = (real_abs y0))).
Definition term3 (x0 : int) (x1 : int) := ((real_sgn (real_of_int x0)) = (real_sgn (real_of_int x1))) /\ ((real_abs (real_of_int x0)) = (real_abs (real_of_int x1))).
Definition term15 (x0 : int) := @eq real (real_of_int (int_abs x0)).
