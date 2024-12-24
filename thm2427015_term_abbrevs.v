Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((~ (x0 = x1)) /\ (~ (x2 = y0))) = (~ ((int_add (int_mul x0 x2) (int_mul x1 y0)) = (int_add (int_mul x0 y0) (int_mul x1 x2))))) x3.
Definition term1 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x1)) /\ (~ (x2 = x3)).
Definition term2 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ~ ((int_add (int_mul x0 x3) (int_mul x2 x1)) = (int_add (int_mul x0 x1) (int_mul x2 x3))).
