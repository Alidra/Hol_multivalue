Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((~ (x0 = x1)) /\ (~ (y0 = y1))) = (~ ((int_add (int_mul x0 y0) (int_mul x1 y1)) = (int_add (int_mul x0 y1) (int_mul x1 y0))))) x2.
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((~ (x0 = y0)) /\ (~ (y1 = y2))) = (~ ((int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_add (int_mul x0 y2) (int_mul y0 y1))))) x1.
Definition term1 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((int_add (int_mul y0 y2) (int_mul y1 y3)) = (int_add (int_mul y0 y3) (int_mul y1 y2))))) x0.
Definition term6 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((~ (x0 = x1)) /\ (~ (x2 = y0))) = (~ ((int_add (int_mul x0 x2) (int_mul x1 y0)) = (int_add (int_mul x0 y0) (int_mul x1 x2)))).
Definition term4 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((~ (x0 = x1)) /\ (~ (y0 = y1))) = (~ ((int_add (int_mul x0 y0) (int_mul x1 y1)) = (int_add (int_mul x0 y1) (int_mul x1 y0)))).
Definition term2 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((~ (x0 = y0)) /\ (~ (y1 = y2))) = (~ ((int_add (int_mul x0 y1) (int_mul y0 y2)) = (int_add (int_mul x0 y2) (int_mul y0 y1)))).
Definition term0 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((int_add (int_mul y0 y2) (int_mul y1 y3)) = (int_add (int_mul y0 y3) (int_mul y1 y2)))).
Definition term7 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((~ (x0 = x1)) /\ (~ (x2 = y0))) = (~ ((int_add (int_mul x0 x2) (int_mul x1 y0)) = (int_add (int_mul x0 y0) (int_mul x1 x2))))) x3.
