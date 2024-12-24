Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term30 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_of_num (NUMERAL 0))) = False.
Definition term1 := int_of_num (NUMERAL 0).
Definition term31 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) = True.
Definition term24 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1.
Definition term26 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) x0.
Definition term29 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term22 (x0 : int) := True -> (int_le (int_of_num (NUMERAL 0)) x0) = (int_le (int_of_num (NUMERAL 0)) x0).
Definition term7 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term19 := @eq int (int_of_num (NUMERAL 0)).
Definition term37 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) = ((y0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x0).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term20 (x0 : int) (x1 : int) (x2 : Prop) := ((x0 = (int_of_num (NUMERAL 0))) = True) -> (True -> (int_le (int_of_num (NUMERAL 0)) x1) = x2) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (True -> x2).
Definition term17 (x0 : int) (x1 : int) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((x0 = (int_of_num (NUMERAL 0))) = x2) -> (x2 -> (int_le (int_of_num (NUMERAL 0)) x1) = y0) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (x2 -> y0)) x3.
Definition term38 := forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) = ((y1 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) y0).
Definition term9 (x0 : int) (x1 : int) := @eq Prop (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term27 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0).
Definition term16 (x0 : int) (x1 : int) (x2 : Prop) := forall y0 : Prop, ((x0 = (int_of_num (NUMERAL 0))) = x2) -> (x2 -> (int_le (int_of_num (NUMERAL 0)) x1) = y0) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (x2 -> y0).
Definition term12 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term14 (x0 : int) (x1 : int) := forall y0 : Prop, forall y1 : Prop, ((x0 = (int_of_num (NUMERAL 0))) = y0) -> (y0 -> (int_le (int_of_num (NUMERAL 0)) x1) = y1) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (y0 -> y1).
Definition term13 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term28 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) x1.
Definition term3 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term18 (x0 : int) (x1 : int) (x2 : Prop) (x3 : Prop) := ((x0 = (int_of_num (NUMERAL 0))) = x2) -> (x2 -> (int_le (int_of_num (NUMERAL 0)) x1) = x3) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (x2 -> x3).
Definition term25 (x0 : int) := True -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term36 (x0 : int) := False -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term23 (x0 : int) (x1 : int) := (True -> (int_le (int_of_num (NUMERAL 0)) x1) = (int_le (int_of_num (NUMERAL 0)) x1)) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (True -> int_le (int_of_num (NUMERAL 0)) x1).
Definition term35 (x0 : int) (x1 : int) := (False -> (int_le (int_of_num (NUMERAL 0)) x1) = (int_le (int_of_num (NUMERAL 0)) x1)) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (False -> int_le (int_of_num (NUMERAL 0)) x1).
Definition term21 (x0 : int) (x1 : int) (x2 : Prop) := (True -> (int_le (int_of_num (NUMERAL 0)) x1) = x2) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (True -> x2).
Definition term5 (x0 : int) := rem x0 (int_of_num (NUMERAL 0)).
Definition term10 (x0 : int) := @eq Prop (int_le (int_of_num (NUMERAL 0)) x0).
Definition term0 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (int_of_num (NUMERAL 0))).
Definition term4 (x0 : int) := (fun y0 : int => (rem y0 (int_of_num (NUMERAL 0))) = y0) x0.
Definition term33 (x0 : int) (x1 : int) (x2 : Prop) := (False -> (int_le (int_of_num (NUMERAL 0)) x1) = x2) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (False -> x2).
Definition term8 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term34 (x0 : int) := False -> (int_le (int_of_num (NUMERAL 0)) x0) = (int_le (int_of_num (NUMERAL 0)) x0).
Definition term6 := int_le (int_of_num (NUMERAL 0)).
Definition term32 (x0 : int) (x1 : int) (x2 : Prop) := ((x0 = (int_of_num (NUMERAL 0))) = False) -> (False -> (int_le (int_of_num (NUMERAL 0)) x1) = x2) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (False -> x2).
Definition term15 (x0 : int) (x1 : int) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = (int_of_num (NUMERAL 0))) = y0) -> (y0 -> (int_le (int_of_num (NUMERAL 0)) x1) = y1) -> ((x0 = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x1) = (y0 -> y1)) x2.
