Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (x0 : int) (x1 : int) := ~ (real_le (real_of_int x0) (real_of_int x1)).
Definition term4 (x0 : int) := (fun y0 : int => forall y1 : int, (int_max y0 y1) = (int_of_real (real_max (real_of_int y0) (real_of_int y1)))) x0.
Definition term12 (x0 : int) (x1 : int) := real_of_int (int_of_real (@COND real (real_le (real_of_int x1) (real_of_int x0)) (real_of_int x0) (real_of_int x1))).
Definition term5 (x0 : int) := forall y0 : int, (int_max x0 y0) = (int_of_real (real_max (real_of_int x0) (real_of_int y0))).
Definition term29 (x0 : int) (x1 : int) := (real_le (real_of_int x0) (real_of_int x1)) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x1).
Definition term36 (x0 : int) := int_of_real (real_of_int x0).
Definition term40 (x0 : int) := forall y0 : int, (real_of_int (int_max x0 y0)) = (real_max (real_of_int x0) (real_of_int y0)).
Definition term35 (x0 : int) (x1 : int) := @eq Prop ((real_of_int (int_of_real (@COND real (real_le (real_of_int x1) (real_of_int x0)) (real_of_int x0) (real_of_int x1)))) = (@COND real (real_le (real_of_int x1) (real_of_int x0)) (real_of_int x0) (real_of_int x1))).
Definition term16 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term20 (x0 : int) (x1 : int) := (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (@COND real (real_le (real_of_int x1) (real_of_int x0)) (real_of_int x0) (real_of_int x1)).
Definition term19 := fun y0 : real => (real_of_int (int_of_real y0)) = y0.
Definition term14 (x0 : int) (x1 : int) := @eq real (real_of_int (int_of_real (@COND real (real_le (real_of_int x1) (real_of_int x0)) (real_of_int x0) (real_of_int x1)))).
Definition term13 (x0 : int) (x1 : int) := @eq real (real_of_int (int_max x0 x1)).
Definition term7 (x0 : int) (x1 : int) := int_of_real (real_max (real_of_int x0) (real_of_int x1)).
Definition term33 (x0 : int) (x1 : int) := ((real_le (real_of_int x1) (real_of_int x0)) -> (real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0)) /\ ((~ (real_le (real_of_int x1) (real_of_int x0))) -> (real_of_int (int_of_real (real_of_int x1))) = (real_of_int x1)).
Definition term24 (x0 : int) := real_of_int (int_of_real (real_of_int x0)).
Definition term28 (x0 : int) (x1 : int) := imp (real_le (real_of_int x0) (real_of_int x1)).
Definition term25 (x0 : int) (x1 : int) := imp (~ (real_le (real_of_int x0) (real_of_int x1))).
Definition term32 (x0 : int) (x1 : int) := and ((real_le (real_of_int x0) (real_of_int x1)) -> (real_of_int (int_of_real (real_of_int x1))) = (real_of_int x1)).
Definition term3 (x0 : real) (x1 : real) := @COND real (real_le x1 x0) x0 x1.
Definition term26 (x0 : int) (x1 : int) := (~ (real_le (real_of_int x1) (real_of_int x0))) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x1).
Definition term37 (x0 : int) := @eq real (real_of_int (int_of_real (real_of_int x0))).
Definition term41 := forall y0 : int, forall y1 : int, (real_of_int (int_max y0 y1)) = (real_max (real_of_int y0) (real_of_int y1)).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_max y1 y0) = (@COND real (real_le y1 y0) y0 y1)) x0.
Definition term30 (x0 : int) (x1 : int) := (real_le (real_of_int x0) (real_of_int x1)) -> (real_of_int (int_of_real (real_of_int x1))) = (real_of_int x1).
Definition term27 (x0 : int) (x1 : int) := (~ (real_le (real_of_int x1) (real_of_int x0))) -> (real_of_int (int_of_real (real_of_int x1))) = (real_of_int x1).
Definition term10 (x0 : int) (x1 : int) := int_of_real (@COND real (real_le (real_of_int x1) (real_of_int x0)) (real_of_int x0) (real_of_int x1)).
Definition term31 (x0 : int) (x1 : int) := and ((real_le (real_of_int x0) (real_of_int x1)) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x1)).
Definition term34 (x0 : int) (x1 : int) := @eq Prop ((fun y0 : real => (real_of_int (int_of_real y0)) = y0) (@COND real (real_le (real_of_int x1) (real_of_int x0)) (real_of_int x0) (real_of_int x1))).
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_max x0 x1).
Definition term18 (x0 : real) (x1 : Prop) (x2 : real) := (x1 -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) x0) /\ ((~ x1) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) x2).
Definition term1 (x0 : real) := forall y0 : real, (real_max y0 x0) = (@COND real (real_le y0 x0) x0 y0).
Definition term22 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term21 (x0 : int) (x1 : int) := ((real_le (real_of_int x1) (real_of_int x0)) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x0)) /\ ((~ (real_le (real_of_int x1) (real_of_int x0))) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x1)).
Definition term23 (x0 : int) := (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x0).
Definition term15 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term6 (x0 : int) (x1 : int) := (fun y0 : int => (int_max x0 y0) = (int_of_real (real_max (real_of_int x0) (real_of_int y0)))) x1.
Definition term38 (x0 : int) := @eq real (real_of_int x0).
Definition term17 (x0 : Prop) (x1 : real) (x2 : real) := (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (@COND real x0 x1 x2).
Definition term8 (x0 : int) (x1 : int) := real_max (real_of_int x0) (real_of_int x1).
Definition term9 (x0 : int) (x1 : int) := @COND real (real_le (real_of_int x1) (real_of_int x0)) (real_of_int x0) (real_of_int x1).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_max y0 x0) = (@COND real (real_le y0 x0) x0 y0)) x1.
