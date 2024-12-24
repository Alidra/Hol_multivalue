Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : int) := fun y0 : int => forall y1 : int, (int_le x0 y0) -> (int_lt y0 y1) -> int_lt x0 y1.
Definition term25 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_le y0 x0) -> (int_lt x0 y1) -> int_lt y0 y1) x1.
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_le x0 y0) -> (int_lt y0 y1) -> int_lt x0 y1) x1.
Definition term46 := int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term53 (x0 : int) := False \/ (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term13 := fun y0 : int => forall y1 : int, forall y2 : int, (int_le y0 y1) -> (int_lt y1 y2) -> int_lt y0 y2.
Definition term12 := fun y0 : int => forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_lt y1 y2)) -> int_lt y0 y2.
Definition term32 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term42 (x0 : int) (x1 : int) := @eq Prop (int_lt (rem x0 x1) x1).
Definition term27 (x0 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0.
Definition term54 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_of_num (NUMERAL 0))) = False.
Definition term39 (x0 : int) (x1 : int) := int_lt (rem x0 x1).
Definition term31 := int_of_num (NUMERAL 0).
Definition term41 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term63 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) = True.
Definition term28 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0) x1.
Definition term55 (x0 : int) := False /\ (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term58 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) x0.
Definition term26 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1) x0.
Definition term7 (x0 : int) (x1 : int) := forall y0 : int, (int_le x1 x0) -> (int_lt x0 y0) -> int_lt x1 y0.
Definition term61 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term24 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_le y1 y0) -> (int_lt y0 y2) -> int_lt y1 y2) x0.
Definition term16 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_le y0 y1) -> (int_lt y1 y2) -> int_lt y0 y2) x0.
Definition term44 := int_lt (int_of_num (NUMERAL 0)).
Definition term5 (x0 : int) (x1 : int) := fun y0 : int => (int_le x1 x0) -> (int_lt x0 y0) -> int_lt x1 y0.
Definition term43 (x0 : int) := @eq Prop (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term62 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term48 := @eq int (int_of_num (NUMERAL 0)).
Definition term2 (x0 : int) (x1 : int) (x2 : int) := ((int_le x1 x0) /\ (int_lt x0 x2)) -> int_lt x1 x2.
Definition term50 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) /\ (int_lt x1 (int_of_num (NUMERAL 0))).
Definition term29 (x0 : int) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> int_lt (rem x0 x1) x1.
Definition term52 (x0 : int) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ ((x0 = (int_of_num (NUMERAL 0))) /\ (int_lt x1 (int_of_num (NUMERAL 0)))).
Definition term45 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term66 (x0 : int) := forall y0 : int, (int_lt (rem x0 y0) y0) = ((int_lt (int_of_num (NUMERAL 0)) y0) \/ ((y0 = (int_of_num (NUMERAL 0))) /\ (int_lt x0 (int_of_num (NUMERAL 0))))).
Definition term20 (x0 : int) (x1 : int) (x2 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, (int_le y0 y1) -> (int_lt y1 y2) -> int_lt y0 y2) -> (int_lt x0 x2) -> int_lt x1 x2.
Definition term19 (x0 : int) (x1 : int) (x2 : int) := (int_lt x0 x2) -> int_lt x1 x2.
Definition term4 (x0 : int) (x1 : int) := fun y0 : int => ((int_le x1 x0) /\ (int_lt x0 y0)) -> int_lt x1 y0.
Definition term36 (x0 : int) := (~ (int_lt x0 x0)) -> (int_lt x0 x0) = False.
Definition term65 (x0 : int) (x1 : int) := ((int_lt (rem x0 x1) x1) -> int_lt (int_of_num (NUMERAL 0)) x1) /\ ((int_lt (int_of_num (NUMERAL 0)) x1) -> int_lt (rem x0 x1) x1).
Definition term67 := forall y0 : int, forall y1 : int, (int_lt (rem y0 y1) y1) = ((int_lt (int_of_num (NUMERAL 0)) y1) \/ ((y1 = (int_of_num (NUMERAL 0))) /\ (int_lt y0 (int_of_num (NUMERAL 0))))).
Definition term22 := forall y0 : int, forall y1 : int, forall y2 : int, (int_le y1 y0) -> (int_lt y0 y2) -> int_lt y1 y2.
Definition term21 (x0 : int) := forall y0 : int, forall y1 : int, (int_le y0 x0) -> (int_lt x0 y1) -> int_lt y0 y1.
Definition term15 := forall y0 : int, forall y1 : int, forall y2 : int, (int_le y0 y1) -> (int_lt y1 y2) -> int_lt y0 y2.
Definition term14 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_lt y1 y2)) -> int_lt y0 y2.
Definition term11 (x0 : int) := forall y0 : int, forall y1 : int, (int_le x0 y0) -> (int_lt y0 y1) -> int_lt x0 y1.
Definition term10 (x0 : int) := forall y0 : int, forall y1 : int, ((int_le x0 y0) /\ (int_lt y0 y1)) -> int_lt x0 y1.
Definition term34 (x0 : int) := (fun y0 : int => ~ (int_lt y0 y0)) x0.
Definition term59 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0).
Definition term40 (x0 : int) (x1 : int) := int_lt (rem x0 x1) x1.
Definition term64 (x0 : int) (x1 : int) := (int_lt (rem x0 x1) x1) -> int_lt (int_of_num (NUMERAL 0)) x1.
Definition term8 (x0 : int) := fun y0 : int => forall y1 : int, ((int_le x0 y0) /\ (int_lt y0 y1)) -> int_lt x0 y1.
Definition term3 (x0 : int) (x1 : int) (x2 : int) := (int_le x1 x0) -> (int_lt x0 x2) -> int_lt x1 x2.
Definition term47 (x0 : int) := or (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term60 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) x1.
Definition term33 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term23 := (forall y0 : int, forall y1 : int, forall y2 : int, (int_le y0 y1) -> (int_lt y1 y2) -> int_lt y0 y2) -> forall y0 : int, forall y1 : int, forall y2 : int, (int_le y1 y0) -> (int_lt y0 y2) -> int_lt y1 y2.
Definition term35 (x0 : int) := ~ (int_lt x0 x0).
Definition term6 (x0 : int) (x1 : int) := forall y0 : int, ((int_le x1 x0) /\ (int_lt x0 y0)) -> int_lt x1 y0.
Definition term38 (x0 : int) := rem x0 (int_of_num (NUMERAL 0)).
Definition term51 (x0 : int) := True /\ (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term57 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) -> (int_lt (rem x0 x1) x1) -> int_lt (int_of_num (NUMERAL 0)) x1.
Definition term49 (x0 : int) := and (x0 = (int_of_num (NUMERAL 0))).
Definition term30 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (int_of_num (NUMERAL 0))).
Definition term37 (x0 : int) := (fun y0 : int => (rem y0 (int_of_num (NUMERAL 0))) = y0) x0.
Definition term18 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le x1 x0) -> (int_lt x0 y0) -> int_lt x1 y0) x2.
Definition term56 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ False.
