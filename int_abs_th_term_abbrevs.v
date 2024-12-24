Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (x0 : int) := ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x0)) /\ ((~ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_neg (real_of_int x0))).
Definition term38 (x0 : int) := and ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x0)).
Definition term30 (x0 : int) := imp (~ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))).
Definition term2 := fun y0 : int => (int_of_real (real_neg (real_of_int y0))) = (int_neg y0).
Definition term46 (x0 : int) := @eq real (real_of_int (int_of_real (real_neg (real_of_int x0)))).
Definition term5 (x0 : int) := (fun y0 : int => (real_of_int (int_neg y0)) = (real_neg (real_of_int y0))) x0.
Definition term27 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term28 (x0 : int) := (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_neg (real_of_int x0)).
Definition term48 (x0 : int) := ~ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term39 (x0 : int) := and ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0)).
Definition term16 (x0 : int) := real_of_int (int_abs x0).
Definition term31 (x0 : int) := (~ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_neg (real_of_int x0)).
Definition term43 (x0 : int) := int_of_real (real_of_int x0).
Definition term21 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term24 := fun y0 : real => (real_of_int (int_of_real y0)) = y0.
Definition term42 (x0 : int) := @eq Prop ((real_of_int (int_of_real (@COND real (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_int x0) (real_neg (real_of_int x0))))) = (@COND real (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_int x0) (real_neg (real_of_int x0)))).
Definition term19 (x0 : int) := @eq real (real_of_int (int_of_real (@COND real (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_int x0) (real_neg (real_of_int x0))))).
Definition term1 := fun y0 : int => (int_neg y0) = (int_of_real (real_neg (real_of_int y0))).
Definition term25 (x0 : int) := (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (@COND real (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_int x0) (real_neg (real_of_int x0))).
Definition term3 := forall y0 : int, (int_neg y0) = (int_of_real (real_neg (real_of_int y0))).
Definition term41 (x0 : int) := @eq Prop ((fun y0 : real => (real_of_int (int_of_real y0)) = y0) (@COND real (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_int x0) (real_neg (real_of_int x0)))).
Definition term12 (x0 : int) := int_of_real (real_abs (real_of_int x0)).
Definition term37 (x0 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0).
Definition term34 (x0 : int) := real_of_int (int_of_real (real_of_int x0)).
Definition term8 (x0 : int) := (fun y0 : int => (int_of_real (real_neg (real_of_int y0))) = (int_neg y0)) x0.
Definition term49 := forall y0 : int, (real_of_int (int_abs y0)) = (real_abs (real_of_int y0)).
Definition term35 (x0 : int) := imp (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term44 (x0 : int) := @eq real (real_of_int (int_of_real (real_of_int x0))).
Definition term9 (x0 : real) := (fun y0 : real => (real_abs y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0))) x0.
Definition term32 (x0 : int) := (~ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) -> (real_of_int (int_of_real (real_neg (real_of_int x0)))) = (real_neg (real_of_int x0)).
Definition term10 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0).
Definition term23 (x0 : real) (x1 : Prop) (x2 : real) := (x1 -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) x0) /\ ((~ x1) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) x2).
Definition term15 (x0 : int) := int_of_real (@COND real (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_int x0) (real_neg (real_of_int x0))).
Definition term7 (x0 : int) := real_neg (real_of_int x0).
Definition term4 := forall y0 : int, (int_of_real (real_neg (real_of_int y0))) = (int_neg y0).
Definition term47 (x0 : int) := @eq real (real_neg (real_of_int x0)).
Definition term33 (x0 : int) := (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x0).
Definition term29 (x0 : int) := real_of_int (int_of_real (real_neg (real_of_int x0))).
Definition term20 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term11 (x0 : int) := (fun y0 : int => (int_abs y0) = (int_of_real (real_abs (real_of_int y0)))) x0.
Definition term14 (x0 : int) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_int x0) (real_neg (real_of_int x0)).
Definition term6 (x0 : int) := real_of_int (int_neg x0).
Definition term36 (x0 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (real_of_int x0).
Definition term45 (x0 : int) := @eq real (real_of_int x0).
Definition term13 (x0 : int) := real_abs (real_of_int x0).
Definition term40 (x0 : int) := ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> (real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0)) /\ ((~ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) -> (real_of_int (int_of_real (real_neg (real_of_int x0)))) = (real_neg (real_of_int x0))).
Definition term22 (x0 : Prop) (x1 : real) (x2 : real) := (fun y0 : real => (real_of_int (int_of_real y0)) = y0) (@COND real x0 x1 x2).
Definition term0 (x0 : int) := int_of_real (real_neg (real_of_int x0)).
Definition term18 (x0 : int) := @eq real (real_of_int (int_abs x0)).
Definition term17 (x0 : int) := real_of_int (int_of_real (@COND real (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_int x0) (real_neg (real_of_int x0)))).
