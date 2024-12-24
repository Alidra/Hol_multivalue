Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term145 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (int_lt (x0 x3) (x0 x1)) /\ (~ (x2 x3)).
Definition term80 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 x1) -> forall y1 : a0, ((x0 y1) = y0) -> x2 y1) -> forall y0 : a0, ((x0 y0) = x1) -> x2 y0.
Definition term69 (a0 : Type') (x0 : a0 -> int) (x1 : nat) (x2 : a0 -> Prop) := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 (int_of_num x1)) -> forall y1 : a0, ((x0 y1) = y0) -> x2 y1) -> forall y0 : a0, ((x0 y0) = (int_of_num x1)) -> x2 y0.
Definition term39 (a0 : Type') (x0 : a0 -> int) (x1 : nat) (x2 : a0 -> Prop) := (forall y0 : nat, (Peano.lt y0 x1) -> forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x2 y1) -> forall y0 : a0, ((x0 y0) = (int_of_num x1)) -> x2 y0.
Definition term360 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> int, (forall y3 : a0, int_le (int_of_num (NUMERAL 0)) (y2 y3)) -> (forall y3 : a0, (forall y4 : a0, (int_lt (y2 y4) (y2 y3)) -> y1 y4) -> y1 y3) -> (forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> forall y4 : a0, ((y2 y4) = y3) -> y1 y4) -> y1 y0.
Definition term359 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> int, (forall y3 : a0, int_le (int_of_num (NUMERAL 0)) (y2 y3)) -> (forall y3 : a0, (forall y4 : a0, (int_lt (y2 y4) (y2 y3)) -> y1 y4) -> y1 y3) -> (~ ((forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> forall y4 : a0, ((y2 y4) = y3) -> y1 y4) -> y1 y0)) -> False.
Definition term21 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) /\ (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0).
Definition term318 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := imp (~ ((~ (int_le (int_of_num (NUMERAL 0)) x3)) \/ ((~ (int_lt x3 (x1 x0))) \/ (~ ((x1 x2) = x3))))).
Definition term189 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := (fun y0 : a0 => fun y1 : a0 => ((int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0)) x2 x3.
Definition term321 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0) := (int_lt (x0 (x1 x2)) (x0 x2)) /\ ((x0 (x1 x2)) = (x0 (x1 x2))).
Definition term0 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term336 := (~ False) -> False.
Definition term48 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) -> forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1) -> forall y0 : nat, forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1.
Definition term368 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (forall y0 : a0, (~ ((x0 y0) = x1)) \/ (x2 y0))).
Definition term367 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (forall y0 : a0, (fun y1 : a0 => (~ ((x0 y1) = x1)) \/ (x2 y1)) y0)).
Definition term241 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (forall y0 : a0, (~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0)))).
Definition term240 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (forall y0 : a0, (fun y1 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y1) = x2)) \/ (x3 y1))) y0)).
Definition term227 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := @eq Prop ((~ (int_lt x2 x0)) \/ (forall y0 : a0, (~ ((x1 y0) = x2)) \/ (x3 y0))).
Definition term226 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := @eq Prop ((~ (int_lt x2 x0)) \/ (forall y0 : a0, (fun y1 : a0 => (~ ((x1 y1) = x2)) \/ (x3 y1)) y0)).
Definition term137 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := imp (forall y0 : a0, (int_lt (x0 y0) (x0 x1)) -> x2 y0).
Definition term116 (a0 : Type') (x0 : a0 -> int) := imp (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)).
Definition term113 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := imp (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0).
Definition term218 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term376 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : int) := (fun y0 : int => forall y1 : a0, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ ((x0 y1) = y0)) \/ (x1 y1))) x2.
Definition term93 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : int) := (fun y0 : int => forall y1 : a0, ((x0 y1) = y0) -> x1 y1) x2.
Definition term387 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ ((x0 x3) = x1)) \/ (x2 x3))).
Definition term261 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 (x1 x0))) \/ ((~ ((x1 x4) = x2)) \/ (x3 x4))).
Definition term233 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (forall y0 : a0, (~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0))).
Definition term202 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0 -> Prop) := forall y0 : a0, ((int_lt (x0 (x1 y0)) (x0 y0)) /\ (~ (x2 (x1 y0)))) \/ (x2 y0).
Definition term212 (x0 : int) := or (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term338 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> int) := (fun y0 : a0 -> int => (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> (~ (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((y0 y3) = y2) -> x0 y3) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2)) -> False) x1.
Definition term61 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (int_lt x2 (int_of_num x0)) -> forall y0 : a0, ((x1 y0) = x2) -> x3 y0.
Definition term323 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := ((int_le (int_of_num (NUMERAL 0)) (x0 (x2 x3))) /\ ((int_lt (x0 (x2 x3)) (x0 x3)) /\ ((x0 (x2 x3)) = (x0 (x2 x3))))) -> x1 (x2 x3).
Definition term62 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term187 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : a0 => fun y1 : a0 => ((int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0).
Definition term112 (x0 : Prop) := ~ (~ x0).
Definition term195 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, exists y1 : a0, ((int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0)).
Definition term194 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, exists y1 : a0, (fun y2 : a0 => fun y3 : a0 => ((int_lt (x0 y3) (x0 y2)) /\ (~ (x1 y3))) \/ (x1 y2)) y0 y1).
Definition term25 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (fun y2 : nat => forall y3 : a0, ((x0 y3) = (int_of_num y2)) -> x1 y3) y1) -> (fun y1 : nat => forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) y0) -> forall y0 : nat, (fun y1 : nat => forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) y0.
Definition term213 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((int_lt x2 x0) -> forall y0 : a0, ((x1 y0) = x2) -> x3 y0).
Definition term342 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := ((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False.
Definition term108 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := ((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False.
Definition term350 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 -> int => (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2) -> x0 x1.
Definition term31 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : nat) (x3 : a0 -> Prop) := (Peano.lt x2 x0) -> forall y0 : a0, ((x1 y0) = (int_of_num x2)) -> x3 y0.
Definition term270 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> ~ (x0 x1).
Definition term388 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> int) (x2 : a0) (x3 : int) := @eq Prop ((x0 x2) \/ ((~ ((x1 x2) = x3)) \/ (~ (int_le (int_of_num (NUMERAL 0)) x3)))).
Definition term75 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : nat) := (fun y0 : int => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) (int_of_num x2).
Definition term256 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (fun y0 : a0 => (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0)))) x4.
Definition term144 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := ~ ((int_lt (x0 x3) (x0 x1)) -> x2 x3).
Definition term214 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 x0)) \/ (forall y0 : a0, (~ ((x1 y0) = x2)) \/ (x3 y0))).
Definition term176 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => ((fun y1 : a0 => (int_lt (x0 y1) (x0 x2)) /\ (~ (x1 y1))) y0) \/ (x1 x2).
Definition term96 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := (int_le (int_of_num (NUMERAL 0)) x1) -> forall y0 : a0, ((x0 y0) = x1) -> x2 y0.
Definition term63 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) (x3 : int) := (int_le (int_of_num (NUMERAL 0)) x3) -> (fun y0 : int => (int_lt y0 (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1) x3.
Definition term155 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := exists y0 : a0, (int_lt (x0 y0) (x0 x1)) /\ (~ (x2 y0)).
Definition term9 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1)) x0.
Definition term200 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0 -> Prop) := fun y0 : a0 => ((int_lt (x0 (x1 y0)) (x0 y0)) /\ (~ (x2 (x1 y0)))) \/ (x2 y0).
Definition term325 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (~ (x0 (x1 x2))) -> x0 (x1 x2).
Definition term203 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : a0 -> a0 => forall y1 : a0, (fun y2 : a0 => fun y3 : a0 => ((int_lt (x0 y3) (x0 y2)) /\ (~ (x1 y3))) \/ (x1 y2)) y1 (y0 y1).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term219 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term207 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := fun y0 : a0 => (~ ((x0 y0) = x1)) \/ (x2 y0).
Definition term343 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False.
Definition term109 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False.
Definition term34 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> (fun y1 : nat => forall y2 : a0, ((x1 y2) = (int_of_num y1)) -> x2 y2) y0.
Definition term71 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : nat, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 (int_of_num y0)) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1.
Definition term43 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) -> forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1.
Definition term146 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) := int_lt (x1 x0) (x1 x2).
Definition term277 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0) := (~ ((x0 (x1 x2)) = (x0 (x1 x2)))) -> (x0 (x1 x2)) = (x0 (x1 x2)).
Definition term32 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> (fun y1 : nat => forall y2 : a0, ((x1 y2) = (int_of_num y1)) -> x2 y2) y0.
Definition term104 (x0 : Prop) := (~ x0) -> False.
Definition term94 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := forall y0 : a0, ((x0 y0) = x1) -> x2 y0.
Definition term300 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> int) (x3 : a0) (x4 : int) := (x0 x3) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x4)) \/ ((~ (int_lt x4 (x2 x1))) \/ (~ ((x2 x3) = x4)))).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term396 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := imp (~ ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (~ ((x0 x1) = x2)))).
Definition term140 (a0 : Type') (x0 : a0 -> int) (x1 : a0) := int_le (int_of_num (NUMERAL 0)) (x0 x1).
Definition term22 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0.
Definition term84 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1.
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (int_lt (int_of_num x0) (int_of_num y0))) x1.
Definition term208 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := forall y0 : a0, (~ ((x0 y0) = x1)) \/ (x2 y0).
Definition term404 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, x0 y0.
Definition term3 (x0 : nat) := forall y0 : nat, (int_lt (int_of_num x0) (int_of_num y0)) = (Peano.lt x0 y0).
Definition term366 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := forall y0 : a0, (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((fun y1 : a0 => (~ ((x0 y1) = x1)) \/ (x2 y1)) y0).
Definition term235 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := forall y0 : a0, (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((fun y1 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y1) = x2)) \/ (x3 y1))) y0).
Definition term221 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := forall y0 : a0, (~ (int_lt x2 x0)) \/ ((fun y1 : a0 => (~ ((x1 y1) = x2)) \/ (x3 y1)) y0).
Definition term169 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => (int_lt (x0 y1) (x0 x1)) /\ (~ (x2 y1))) y0).
Definition term238 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y1) = x2)) \/ (x3 y1))) y0.
Definition term27 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : nat) := (fun y0 : nat => forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1) x2.
Definition term324 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := x0 (x1 x2).
Definition term239 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := forall y0 : a0, (fun y1 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y1) = x2)) \/ (x3 y1))) y0.
Definition term225 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := forall y0 : a0, (fun y1 : a0 => (~ ((x0 y1) = x1)) \/ (x2 y1)) y0.
Definition term228 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (~ (int_lt x2 x0)) \/ ((fun y0 : a0 => (~ ((x1 y0) = x2)) \/ (x3 y0)) x4).
Definition term272 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term358 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0 -> int, (forall y3 : a0, int_le (int_of_num (NUMERAL 0)) (y2 y3)) -> (forall y3 : a0, (forall y4 : a0, (int_lt (y2 y4) (y2 y3)) -> y1 y4) -> y1 y3) -> (forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> forall y4 : a0, ((y2 y4) = y3) -> y1 y4) -> y1 y0.
Definition term357 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0 -> int, (forall y3 : a0, int_le (int_of_num (NUMERAL 0)) (y2 y3)) -> (forall y3 : a0, (forall y4 : a0, (int_lt (y2 y4) (y2 y3)) -> y1 y4) -> y1 y3) -> (~ ((forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> forall y4 : a0, ((y2 y4) = y3) -> y1 y4) -> y1 y0)) -> False.
Definition term392 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := (~ ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ ((x0 x3) = x1)))) -> x2 x3.
Definition term399 (a0 : Type') (x0 : a0 -> int) (x1 : a0) := (int_le (int_of_num (NUMERAL 0)) (x0 x1)) /\ ((x0 x1) = (x0 x1)).
Definition term406 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> int, ((forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) /\ (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1)) -> forall y1 : a0, x0 y1.
Definition term158 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (~ (forall y0 : a0, (int_lt (x0 y0) (x0 x2)) -> x1 y0)) \/ (x1 x2).
Definition term274 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> int) (x2 : a0) := (~ (int_lt (x1 (x0 x2)) (x1 x2))) -> int_lt (x1 (x0 x2)) (x1 x2).
Definition term70 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : nat => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 (int_of_num y0)) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1.
Definition term41 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.lt y1 y0) -> forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) -> forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1.
Definition term166 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (int_lt (x0 y0) (x0 x1)) /\ (~ (x2 y0))) x3.
Definition term319 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := imp ((int_le (int_of_num (NUMERAL 0)) x3) /\ ((int_lt x3 (x1 x0)) /\ ((x1 x2) = x3))).
Definition term52 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : nat, (int_lt (int_of_num y0) (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = (int_of_num y0)) -> x2 y1.
Definition term269 (x0 : Prop) := (~ x0) -> x0.
Definition term130 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (int_le (int_of_num (NUMERAL 0)) x2) -> (int_lt x2 x0) -> forall y0 : a0, ((x1 y0) = x2) -> x3 y0.
Definition term333 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := (x1 (x0 x2)) -> x1 x2.
Definition term250 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> int) (x2 : a0) := int_lt (x1 (x0 x2)) (x1 x2).
Definition term35 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> forall y1 : a0, ((x1 y1) = (int_of_num y0)) -> x2 y1.
Definition term81 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) -> (fun y0 : int => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) x2.
Definition term303 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term185 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : a0, exists y1 : a0, (fun y2 : a0 => fun y3 : a0 => ((int_lt (x0 y3) (x0 y2)) /\ (~ (x1 y3))) \/ (x1 y2)) y0 y1.
Definition term183 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, exists y1 : a0, x0 y0 y1.
Definition term181 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term236 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term369 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((fun y0 : a0 => (~ ((x0 y0) = x1)) \/ (x2 y0)) x3).
Definition term316 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := (int_lt x3 (x1 x0)) /\ ((x1 x2) = x3).
Definition term383 (a0 : Type') (x0 : int) (x1 : a0 -> Prop) (x2 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (x1 x2).
Definition term354 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3) -> y0 x0.
Definition term353 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> (~ ((forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3) -> y0 x0)) -> False.
Definition term123 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> (int_lt y3 y2) -> forall y4 : a0, ((y1 y4) = y3) -> y0 y4) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3.
Definition term122 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> (~ (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> (int_lt y3 y2) -> forall y4 : a0, ((y1 y4) = y3) -> y0 y4) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3)) -> False.
Definition term50 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : nat) (x3 : a0 -> Prop) := (int_lt (int_of_num x2) (int_of_num x0)) -> forall y0 : a0, ((x1 y0) = (int_of_num x2)) -> x3 y0.
Definition term192 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, (fun y1 : a0 => fun y2 : a0 => ((int_lt (x0 y2) (x0 y1)) /\ (~ (x1 y2))) \/ (x1 y1)) x2 y0.
Definition term173 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := or ((int_lt (x0 x3) (x0 x1)) /\ (~ (x2 x3))).
Definition term251 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ (x0 (x1 x2)).
Definition term156 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := or (~ (forall y0 : a0, (int_lt (x0 y0) (x0 x1)) -> x2 y0)).
Definition term78 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := @eq Prop (forall y0 : nat, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 (int_of_num y0)) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1).
Definition term59 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := @eq Prop (forall y0 : nat, (int_lt (int_of_num y0) (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = (int_of_num y0)) -> x2 y1).
Definition term298 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := (~ (int_lt x3 (x1 x0))) \/ (~ ((x1 x2) = x3)).
Definition term314 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0) := and (int_lt x0 (x1 x2)).
Definition term289 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : int) (x3 : a0 -> int) (x4 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((x0 x1) \/ ((~ ((x3 x1) = x2)) \/ (~ (int_lt x2 (x3 x4))))).
Definition term193 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, (fun y2 : a0 => fun y3 : a0 => ((int_lt (x0 y3) (x0 y2)) /\ (~ (x1 y3))) \/ (x1 y2)) y0 y1.
Definition term165 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, ((fun y1 : a0 => (int_lt (x0 y1) (x0 x2)) /\ (~ (x1 y1))) y0) \/ (x1 x2).
Definition term273 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0 -> int) (x3 : a0) := (~ (x0 x3)) -> int_lt (x2 (x1 x3)) (x2 x3).
Definition term311 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0) := ~ (~ (int_lt x0 (x1 x2))).
Definition term306 (x0 : int) := ~ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term295 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : int) (x3 : a0 -> int) (x4 : a0) := (x0 x1) \/ ((~ ((x3 x1) = x2)) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (~ (int_lt x2 (x3 x4))))).
Definition term290 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : int) (x3 : a0 -> int) (x4 : a0) := (x0 x1) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ ((x3 x1) = x2)) \/ (~ (int_lt x2 (x3 x4))))).
Definition term266 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0) := int_le (int_of_num (NUMERAL 0)) (x0 (x1 x2)).
Definition term76 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : nat => (fun y1 : int => (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((x0 y3) = y2) -> x1 y3) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) (int_of_num y0).
Definition term57 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : nat => (fun y1 : int => (int_lt y1 (int_of_num x0)) -> forall y2 : a0, ((x1 y2) = y1) -> x2 y2) (int_of_num y0).
Definition term313 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0) := and (~ (~ (int_lt x0 (x1 x2)))).
Definition term279 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term164 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (fun y1 : a0 => (int_lt (x0 y1) (x0 x2)) /\ (~ (x1 y1))) y0) \/ (x1 x2).
Definition term402 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> (~ ((forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3) -> y0 x0)) -> False) x1.
Definition term89 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : nat) := (fun y0 : int => forall y1 : a0, ((x0 y1) = y0) -> x1 y1) (int_of_num x2).
Definition term364 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (forall y1 : a0, (~ ((x0 y1) = y0)) \/ (x1 y1)).
Definition term5 := fun y0 : nat => forall y1 : nat, (int_lt (int_of_num y0) (int_of_num y1)) = (Peano.lt y0 y1).
Definition term102 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : nat, forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1) -> x1 x2.
Definition term310 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := (~ (~ (int_lt x3 (x1 x0)))) /\ (~ (~ ((x1 x2) = x3))).
Definition term98 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1.
Definition term309 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := ~ ((~ (int_lt x3 (x1 x0))) \/ (~ ((x1 x2) = x3))).
Definition term95 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) -> (fun y0 : int => forall y1 : a0, ((x0 y1) = y0) -> x1 y1) x2.
Definition term51 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : nat => (int_lt (int_of_num y0) (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = (int_of_num y0)) -> x2 y1.
Definition term168 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (int_lt (x0 y1) (x0 x1)) /\ (~ (x2 y1))) y0.
Definition term91 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := @eq Prop (forall y0 : nat, (fun y1 : int => forall y2 : a0, ((x0 y2) = y1) -> x1 y2) (int_of_num y0)).
Definition term77 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := @eq Prop (forall y0 : nat, (fun y1 : int => (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((x0 y3) = y2) -> x1 y3) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) (int_of_num y0)).
Definition term58 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := @eq Prop (forall y0 : nat, (fun y1 : int => (int_lt y1 (int_of_num x0)) -> forall y2 : a0, ((x1 y2) = y1) -> x2 y2) (int_of_num y0)).
Definition term153 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (int_lt (x0 y1) (x0 x1)) -> x2 y1) y0).
Definition term201 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0 -> a0) := forall y0 : a0, (fun y1 : a0 => fun y2 : a0 => ((int_lt (x0 y2) (x0 y1)) /\ (~ (x1 y2))) \/ (x1 y1)) y0 (x2 y0).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> int => (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((y0 y3) = y2) -> x0 y3) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2.
Definition term167 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (int_lt (x0 y1) (x0 x1)) /\ (~ (x2 y1))) y0.
Definition term234 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (forall y0 : a0, (fun y1 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y1) = x2)) \/ (x3 y1))) y0).
Definition term299 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x3)) \/ ((~ (int_lt x3 (x1 x0))) \/ (~ ((x1 x2) = x3))).
Definition term224 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (~ ((x0 y1) = x1)) \/ (x2 y1)) y0.
Definition term403 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> int) := (fun y0 : a0 -> int => (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> (~ ((forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2) -> x0 x1)) -> False) x2.
Definition term161 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : a0, (exists y1 : a0, (int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0).
Definition term103 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2.
Definition term260 (a0 : Type') (x0 : int) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> int) (x4 : a0) := (fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((~ (int_lt x0 y0)) \/ ((~ ((x3 x2) = x0)) \/ (x1 x2)))) (x3 x4).
Definition term262 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) (x4 : int) := @eq Prop ((fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ (int_lt x1 y0)) \/ ((~ ((x0 x3) = x1)) \/ (x2 x3)))) x4).
Definition term132 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 x0) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1.
Definition term85 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1.
Definition term67 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1.
Definition term92 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := @eq Prop (forall y0 : nat, forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1).
Definition term45 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := imp (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) -> forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1).
Definition term44 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := imp (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (fun y2 : nat => forall y3 : a0, ((x0 y3) = (int_of_num y2)) -> x1 y3) y1) -> (fun y1 : nat => forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) y0).
Definition term37 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := imp (forall y0 : nat, (Peano.lt y0 x0) -> forall y1 : a0, ((x1 y1) = (int_of_num y0)) -> x2 y1).
Definition term36 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := imp (forall y0 : nat, (Peano.lt y0 x0) -> (fun y1 : nat => forall y2 : a0, ((x1 y2) = (int_of_num y1)) -> x2 y2) y0).
Definition term322 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0) := (int_le (int_of_num (NUMERAL 0)) (x0 (x1 x2))) /\ ((int_lt (x0 (x1 x2)) (x0 x2)) /\ ((x0 (x1 x2)) = (x0 (x1 x2)))).
Definition term372 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := fun y0 : a0 => (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ ((x0 y0) = x1)) \/ (x2 y0)).
Definition term40 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.lt y1 y0) -> (fun y2 : nat => forall y3 : a0, ((x0 y3) = (int_of_num y2)) -> x1 y3) y1) -> (fun y1 : nat => forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) y0.
Definition term191 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => ((int_lt (x0 y2) (x0 y1)) /\ (~ (x1 y2))) \/ (x1 y1)) x2 y0.
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> False.
Definition term174 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 => (int_lt (x0 y0) (x0 x3)) /\ (~ (x2 y0))) x1) \/ (x2 x3).
Definition term220 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (~ (int_lt x2 x0)) \/ (forall y0 : a0, (fun y1 : a0 => (~ ((x1 y1) = x2)) \/ (x3 y1)) y0).
Definition term287 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : int) (x3 : a0 -> int) (x4 : a0) := (~ ((x3 x1) = x2)) \/ ((x0 x1) \/ (~ (int_lt x2 (x3 x4)))).
Definition term278 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0) := ~ ((x0 (x1 x2)) = (x0 (x1 x2))).
Definition term253 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0 -> Prop) := forall y0 : a0, ((int_lt (x0 (x1 y0)) (x0 y0)) \/ (x2 y0)) /\ ((~ (x2 (x1 y0))) \/ (x2 y0)).
Definition term291 (a0 : Type') (x0 : a0) (x1 : int) (x2 : a0 -> int) (x3 : a0) := (~ ((x2 x0) = x1)) \/ (~ (int_lt x1 (x2 x3))).
Definition term286 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := or (~ ((x0 x1) = x2)).
Definition term327 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((~ (x1 (x0 x2))) \/ (x1 x2)).
Definition term328 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := @eq Prop ((x0 x2) \/ (~ (x0 (x1 x2)))).
Definition term384 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : int) := (x0 x1) \/ (~ (int_le (int_of_num (NUMERAL 0)) x2)).
Definition term329 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (x1 (x0 x2)))) -> x1 x2.
Definition term339 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False.
Definition term244 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := fun y0 : a0 => (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((fun y1 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y1) = x2)) \/ (x3 y1))) y0).
Definition term17 (x0 : nat -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1) -> x0 y0.
Definition term175 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := ((int_lt (x0 x1) (x0 x3)) /\ (~ (x2 x1))) \/ (x2 x3).
Definition term138 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, (int_lt (x0 y0) (x0 x2)) -> x1 y0) -> x1 x2.
Definition term302 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term377 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ ((x0 y0) = x1)) \/ (x2 y0))) x3.
Definition term24 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : nat, forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1.
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) = (int_lt (int_of_num y0) (int_of_num y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (int_lt (int_of_num y0) (int_of_num y1)) = (Peano.lt y0 y1).
Definition term330 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := ~ (~ (x0 (x1 x2))).
Definition term341 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False.
Definition term107 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False.
Definition term284 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0) (x3 : a0 -> Prop) (x4 : a0) := (~ (int_lt x0 (x1 x2))) \/ (x3 x4).
Definition term106 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1).
Definition term254 (a0 : Type') (x0 : a0 -> int) (x1 : a0) := (fun y0 : a0 => int_le (int_of_num (NUMERAL 0)) (x0 y0)) x1.
Definition term128 (x0 : int) (x1 : int) := imp (int_lt x0 x1).
Definition term141 (a0 : Type') (x0 : a0 -> int) := fun y0 : a0 => int_le (int_of_num (NUMERAL 0)) (x0 y0).
Definition term255 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0 -> Prop) (x3 : int) := (fun y0 : int => forall y1 : a0, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 x0)) \/ ((~ ((x1 y1) = y0)) \/ (x2 y1)))) x3.
Definition term83 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((x0 y3) = y2) -> x1 y3) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) y0.
Definition term65 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (int_lt y1 (int_of_num x0)) -> forall y2 : a0, ((x1 y2) = y1) -> x2 y2) y0.
Definition term177 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => ((int_lt (x0 y0) (x0 x2)) /\ (~ (x1 y0))) \/ (x1 x2).
Definition term11 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term74 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : int => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1.
Definition term126 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x3) = x1) -> x2 x3.
Definition term1 (x0 : nat) := fun y0 : nat => (int_lt (int_of_num x0) (int_of_num y0)) = (Peano.lt x0 y0).
Definition term375 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : int, forall y1 : a0, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ ((x0 y1) = y0)) \/ (x1 y1)).
Definition term248 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : int, forall y1 : a0, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 x0)) \/ ((~ ((x1 y1) = y0)) \/ (x2 y1))).
Definition term288 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : int) (x3 : a0 -> int) (x4 : a0) := (x0 x1) \/ ((~ ((x3 x1) = x2)) \/ (~ (int_lt x2 (x3 x4)))).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term337 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> (~ (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> (int_lt y3 y2) -> forall y4 : a0, ((y1 y4) = y3) -> y0 y4) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3)) -> False) x0.
Definition term405 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := ((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) /\ (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0)) -> forall y0 : a0, x1 y0.
Definition term362 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (forall y0 : a0, (~ ((x0 y0) = x1)) \/ (x2 y0)).
Definition term361 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (forall y0 : a0, ((x0 y0) = x1) -> x2 y0).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> int, (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((y0 y3) = y2) -> x0 y3) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2.
Definition term304 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := ~ ((~ (int_le (int_of_num (NUMERAL 0)) x3)) \/ ((~ (int_lt x3 (x1 x0))) \/ (~ ((x1 x2) = x3)))).
Definition term38 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : nat) := (forall y0 : nat, (Peano.lt y0 x2) -> (fun y1 : nat => forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) y0) -> (fun y0 : nat => forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1) x2.
Definition term111 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := ~ (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)).
Definition term395 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) /\ ((x0 x1) = x2).
Definition term340 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := ~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2).
Definition term204 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : a0 -> a0 => forall y1 : a0, ((int_lt (x0 (y0 y1)) (x0 y1)) /\ (~ (x1 (y0 y1)))) \/ (x1 y1).
Definition term154 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => (int_lt (x0 y0) (x0 x1)) /\ (~ (x2 y0)).
Definition term197 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := (fun y0 : a0 => ((int_lt (x0 y0) (x0 x3)) /\ (~ (x1 y0))) \/ (x1 x3)) (x2 x3).
Definition term105 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False.
Definition term296 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 (x1 x0))) \/ ((~ ((x1 x4) = x2)) \/ (x3 x4)))).
Definition term263 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 x0)) \/ ((~ ((x1 x4) = x2)) \/ (x3 x4)))).
Definition term230 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := fun y0 : a0 => (~ (int_lt x2 x0)) \/ ((fun y1 : a0 => (~ ((x1 y1) = x2)) \/ (x3 y1)) y0).
Definition term391 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> int) (x2 : a0) (x3 : int) := (x0 x2) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x3)) \/ (~ ((x1 x2) = x3))).
Definition term386 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> int) (x2 : a0) (x3 : int) := (x0 x2) \/ ((~ ((x1 x2) = x3)) \/ (~ (int_le (int_of_num (NUMERAL 0)) x3))).
Definition term188 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => fun y1 : a0 => ((int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0)) x2.
Definition term293 (a0 : Type') (x0 : a0) (x1 : int) (x2 : a0 -> int) (x3 : a0) := (~ ((x2 x0) = x1)) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (int_lt x1 (x2 x3)))).
Definition term292 (a0 : Type') (x0 : a0) (x1 : int) (x2 : a0 -> int) (x3 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ ((x2 x0) = x1)) \/ (~ (int_lt x1 (x2 x3)))).
Definition term249 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0 -> Prop) (x3 : a0) := ((int_lt (x0 (x1 x3)) (x0 x3)) \/ (x2 x3)) /\ ((~ (x2 (x1 x3))) \/ (x2 x3)).
Definition term267 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) (x0 (x1 x2)))) -> int_le (int_of_num (NUMERAL 0)) (x0 (x1 x2)).
Definition term331 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := imp (~ (~ (x0 (x1 x2)))).
Definition term172 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := or ((fun y0 : a0 => (int_lt (x0 y0) (x0 x1)) /\ (~ (x2 y0))) x3).
Definition term389 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (~ ((x0 x1) = x2)).
Definition term90 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : nat => (fun y1 : int => forall y2 : a0, ((x0 y2) = y1) -> x1 y2) (int_of_num y0).
Definition term326 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := (x0 x2) \/ (~ (x0 (x1 x2))).
Definition term29 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term307 (x0 : int) := and (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term97 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : a0, ((x0 y2) = y1) -> x1 y2) y0.
Definition term374 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : int => forall y1 : a0, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ ((x0 y1) = y0)) \/ (x1 y1)).
Definition term247 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : int => forall y1 : a0, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 x0)) \/ ((~ ((x1 y1) = y0)) \/ (x2 y1))).
Definition term380 (a0 : Type') (x0 : a0 -> int) (x1 : a0) := (~ ((x0 x1) = (x0 x1))) -> (x0 x1) = (x0 x1).
Definition term407 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> int, ((forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) /\ (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2)) -> forall y2 : a0, y0 y2.
Definition term356 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3) -> y0 x0.
Definition term355 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> (~ ((forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3) -> y0 x0)) -> False.
Definition term125 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> (int_lt y3 y2) -> forall y4 : a0, ((y1 y4) = y3) -> y0 y4) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3.
Definition term124 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> int, (forall y2 : a0, int_le (int_of_num (NUMERAL 0)) (y1 y2)) -> (forall y2 : a0, (forall y3 : a0, (int_lt (y1 y3) (y1 y2)) -> y0 y3) -> y0 y2) -> (~ (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> (int_lt y3 y2) -> forall y4 : a0, ((y1 y4) = y3) -> y0 y4) -> forall y3 : a0, ((y1 y3) = y2) -> y0 y3)) -> False.
Definition term56 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) (x3 : nat) := (fun y0 : int => (int_lt y0 (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1) (int_of_num x3).
Definition term344 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False) -> ((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False.
Definition term110 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False) -> ((forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False) -> (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False.
Definition term135 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := fun y0 : a0 => (int_lt (x0 y0) (x0 x1)) -> x2 y0.
Definition term282 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := ~ ((x0 x1) = x2).
Definition term115 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1.
Definition term136 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : a0, (int_lt (x0 y0) (x0 x1)) -> x2 y0.
Definition term28 (a0 : Type') (x0 : a0 -> int) (x1 : nat) (x2 : a0 -> Prop) := forall y0 : a0, ((x0 y0) = (int_of_num x1)) -> x2 y0.
Definition term332 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a0) (x2 : a0) := imp (x0 (x1 x2)).
Definition term199 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0 -> a0) := fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => ((int_lt (x0 y2) (x0 y1)) /\ (~ (x1 y2))) \/ (x1 y1)) y0 (x2 y0).
Definition term151 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (int_lt (x0 y0) (x0 x1)) -> x2 y0) x3.
Definition term379 (a0 : Type') (x0 : a0 -> int) (x1 : a0) := ~ (int_le (int_of_num (NUMERAL 0)) (x0 x1)).
Definition term308 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term246 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := forall y0 : a0, (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0))).
Definition term345 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := ~ (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)).
Definition term371 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := fun y0 : a0 => (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((fun y1 : a0 => (~ ((x0 y1) = x1)) \/ (x2 y1)) y0).
Definition term229 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (~ (int_lt x2 x0)) \/ ((~ ((x1 x4) = x2)) \/ (x3 x4)).
Definition term60 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) (x3 : int) := (fun y0 : int => (int_lt y0 (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1) x3.
Definition term348 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2.
Definition term209 (x0 : int) (x1 : int) := or (~ (int_lt x0 x1)).
Definition term265 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 (x0 x2))) \/ (x1 x2).
Definition term46 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : nat => (fun y1 : nat => forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) y0.
Definition term347 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2.
Definition term349 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 -> int => (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> (~ ((forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2) -> x0 x1)) -> False.
Definition term118 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> int => (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> (~ (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((y0 y3) = y2) -> x0 y3) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2)) -> False.
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (int_lt (int_of_num y0) (int_of_num y1))) x0.
Definition term373 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := forall y0 : a0, (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ ((x0 y0) = x1)) \/ (x2 y0)).
Definition term232 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := forall y0 : a0, (~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0)).
Definition term150 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => (int_lt (x0 y1) (x0 x1)) -> x2 y1) y0).
Definition term129 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (int_lt x2 x0) -> forall y0 : a0, ((x1 y0) = x2) -> x3 y0.
Definition term258 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ (int_lt x1 y0)) \/ ((~ ((x0 x3) = x1)) \/ (x2 x3))).
Definition term30 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) (x3 : nat) := (Peano.lt x3 x0) -> (fun y0 : nat => forall y1 : a0, ((x1 y1) = (int_of_num y0)) -> x2 y1) x3.
Definition term79 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : int) := (fun y0 : int => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) x2.
Definition term10 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term352 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0 -> int, (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2) -> x0 x1.
Definition term72 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : nat, (fun y1 : int => (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((x0 y3) = y2) -> x1 y3) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) (int_of_num y0).
Definition term53 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : nat, (fun y1 : int => (int_lt y1 (int_of_num x0)) -> forall y2 : a0, ((x1 y2) = y1) -> x2 y2) (int_of_num y0).
Definition term351 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0 -> int, (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> (~ ((forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2) -> x0 x1)) -> False.
Definition term120 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> int, (forall y1 : a0, int_le (int_of_num (NUMERAL 0)) (y0 y1)) -> (forall y1 : a0, (forall y2 : a0, (int_lt (y0 y2) (y0 y1)) -> x0 y2) -> x0 y1) -> (~ (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((y0 y3) = y2) -> x0 y3) -> forall y2 : a0, ((y0 y2) = y1) -> x0 y2)) -> False.
Definition term312 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0) := int_lt x0 (x1 x2).
Definition term382 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x0 x3) = x1)) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (x2 x3)).
Definition term370 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ ((x0 x3) = x1)) \/ (x2 x3)).
Definition term171 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, (int_lt (x0 y0) (x0 x2)) /\ (~ (x1 y0))) \/ (x1 x2)).
Definition term170 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (int_lt (x0 y1) (x0 x2)) /\ (~ (x1 y1))) y0) \/ (x1 x2)).
Definition term152 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := ~ ((fun y0 : a0 => (int_lt (x0 y0) (x0 x1)) -> x2 y0) x3).
Definition term245 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := fun y0 : a0 => (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0))).
Definition term280 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (~ (int_lt x2 (x1 x0))) \/ ((~ ((x1 x4) = x2)) \/ (x3 x4)).
Definition term211 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (~ (int_lt x2 x0)) \/ (forall y0 : a0, (~ ((x1 y0) = x2)) \/ (x3 y0)).
Definition term210 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (~ (int_lt x2 x0)) \/ (forall y0 : a0, ((x1 y0) = x2) -> x3 y0).
Definition term393 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := ~ ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (~ ((x0 x1) = x2))).
Definition term297 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : int) (x3 : a0 -> int) (x4 : a0) := @eq Prop ((x0 x1) \/ ((~ ((x3 x1) = x2)) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ (~ (int_lt x2 (x3 x4)))))).
Definition term42 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (fun y2 : nat => forall y3 : a0, ((x0 y3) = (int_of_num y2)) -> x1 y3) y1) -> (fun y1 : nat => forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) y0.
Definition term394 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x2))) /\ (~ (~ ((x0 x1) = x2))).
Definition term23 (a0 : Type') (x0 : a0 -> int) := forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0).
Definition term99 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1.
Definition term82 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := (int_le (int_of_num (NUMERAL 0)) x1) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 x1) -> forall y1 : a0, ((x0 y1) = y0) -> x2 y1) -> forall y0 : a0, ((x0 y0) = x1) -> x2 y0.
Definition term283 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0) := ~ (int_lt x0 (x1 x2)).
Definition term346 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1) -> x1 x2)) -> False.
Definition term114 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1)) -> False.
Definition term160 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : a0, (int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0).
Definition term87 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : a0, ((x0 y2) = y1) -> x1 y2) y0.
Definition term73 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (int_lt y2 y1) -> forall y3 : a0, ((x0 y3) = y2) -> x1 y3) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) y0.
Definition term54 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (int_lt y1 (int_of_num x0)) -> forall y2 : a0, ((x1 y2) = y1) -> x2 y2) y0.
Definition term259 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) (x4 : int) := (fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ (int_lt x1 y0)) \/ ((~ ((x0 x3) = x1)) \/ (x2 x3)))) x4.
Definition term243 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 x0)) \/ ((~ ((x1 x4) = x2)) \/ (x3 x4))).
Definition term305 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x3))) /\ (~ ((~ (int_lt x3 (x1 x0))) \/ (~ ((x1 x2) = x3)))).
Definition term315 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := ~ (~ ((x0 x1) = x2)).
Definition term275 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> int) (x2 : a0) := ~ (int_lt (x1 (x0 x2)) (x1 x2)).
Definition term335 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term33 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> forall y1 : a0, ((x1 y1) = (int_of_num y0)) -> x2 y1.
Definition term15 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1) x0.
Definition term49 (x0 : nat) (x1 : nat) := imp (int_lt (int_of_num x0) (int_of_num x1)).
Definition term237 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (fun y0 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0))) x4.
Definition term398 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := ((int_le (int_of_num (NUMERAL 0)) x1) /\ ((x0 x3) = x1)) -> x2 x3.
Definition term365 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (forall y0 : a0, (fun y1 : a0 => (~ ((x0 y1) = x1)) \/ (x2 y1)) y0).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (int_lt (int_of_num x0) (int_of_num y0)).
Definition term301 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (~ ((~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((~ (int_lt x2 (x1 x0))) \/ (~ ((x1 x4) = x2))))) -> x3 x4.
Definition term198 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0 -> Prop) (x3 : a0) := ((int_lt (x0 (x1 x3)) (x0 x3)) /\ (~ (x2 (x1 x3)))) \/ (x2 x3).
Definition term378 (a0 : Type') (x0 : a0 -> int) (x1 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) (x0 x1))) -> int_le (int_of_num (NUMERAL 0)) (x0 x1).
Definition term281 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0) (x3 : a0 -> Prop) (x4 : a0) := (~ ((x1 x4) = x0)) \/ ((~ (int_lt x0 (x1 x2))) \/ (x3 x4)).
Definition term285 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : int) (x3 : a0 -> int) (x4 : a0) := (x0 x1) \/ (~ (int_lt x2 (x3 x4))).
Definition term264 (a0 : Type') (x0 : a0 -> a0) (x1 : a0 -> int) (x2 : a0 -> Prop) (x3 : a0) := (int_lt (x1 (x0 x3)) (x1 x3)) \/ (x2 x3).
Definition term216 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 x0)) \/ (forall y1 : a0, (~ ((x1 y1) = y0)) \/ (x2 y1))).
Definition term131 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 x0) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1.
Definition term19 (x0 : nat -> Prop) := (forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1) -> forall y0 : nat, x0 y0.
Definition term16 (x0 : nat -> Prop) := (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1) -> x0 y0) -> forall y0 : nat, x0 y0.
Definition term14 := forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1.
Definition term363 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (forall y1 : a0, (~ ((x0 y1) = y0)) \/ (x1 y1)).
Definition term223 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (~ ((x0 y0) = x1)) \/ (x2 y0)) x3.
Definition term400 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := ((int_le (int_of_num (NUMERAL 0)) (x0 x2)) /\ ((x0 x2) = (x0 x2))) -> x1 x2.
Definition term127 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) := fun y0 : a0 => ((x0 y0) = x1) -> x2 y0.
Definition term134 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (int_lt (x0 x3) (x0 x1)) -> x2 x3.
Definition term180 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : a0, exists y1 : a0, ((int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0).
Definition term385 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) (x3 : int) := (~ ((x0 x2) = x3)) \/ ((x1 x2) \/ (~ (int_le (int_of_num (NUMERAL 0)) x3))).
Definition term206 (a0 : Type') (x0 : a0 -> int) (x1 : int) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x0 x3) = x1)) \/ (x2 x3).
Definition term88 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : int => forall y1 : a0, ((x0 y1) = y0) -> x1 y1.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) = (int_lt (int_of_num x0) (int_of_num y0)).
Definition term139 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0.
Definition term215 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term20 := (forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1) -> forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1.
Definition term190 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := (fun y0 : a0 => ((int_lt (x0 y0) (x0 x2)) /\ (~ (x1 y0))) \/ (x1 x2)) x3.
Definition term231 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := fun y0 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0)).
Definition term86 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : nat, (fun y1 : int => forall y2 : a0, ((x0 y2) = y1) -> x1 y2) (int_of_num y0).
Definition term196 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0 -> a0) (x3 : a0) := (fun y0 : a0 => fun y1 : a0 => ((int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0)) x3 (x2 x3).
Definition term133 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0 -> Prop) := imp (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 x0) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1).
Definition term101 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := imp (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1).
Definition term68 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := imp (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1).
Definition term276 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0) := x0 (x1 x2).
Definition term242 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := (~ (int_le (int_of_num (NUMERAL 0)) x2)) \/ ((fun y0 : a0 => (~ (int_lt x2 x0)) \/ ((~ ((x1 y0) = x2)) \/ (x3 y0))) x4).
Definition term397 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := imp ((int_le (int_of_num (NUMERAL 0)) x2) /\ ((x0 x1) = x2)).
Definition term179 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, ((int_lt (x0 y1) (x0 y0)) /\ (~ (x1 y1))) \/ (x1 y0).
Definition term159 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (int_lt (x0 y0) (x0 x2)) /\ (~ (x1 y0))) \/ (x1 x2).
Definition term117 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := (forall y0 : a0, int_le (int_of_num (NUMERAL 0)) (x0 y0)) -> (forall y0 : a0, (forall y1 : a0, (int_lt (x0 y1) (x0 y0)) -> x1 y1) -> x1 y0) -> forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (int_lt y1 y0) -> forall y2 : a0, ((x0 y2) = y1) -> x1 y2) -> forall y1 : a0, ((x0 y1) = y0) -> x1 y1.
Definition term252 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0 -> Prop) := fun y0 : a0 => ((int_lt (x0 (x1 y0)) (x0 y0)) \/ (x2 y0)) /\ ((~ (x2 (x1 y0))) \/ (x2 y0)).
Definition term47 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := forall y0 : nat, (fun y1 : nat => forall y2 : a0, ((x0 y2) = (int_of_num y1)) -> x1 y2) y0.
Definition term205 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := exists y0 : a0 -> a0, forall y1 : a0, ((int_lt (x0 (y0 y1)) (x0 y1)) /\ (~ (x1 (y0 y1)))) \/ (x1 y1).
Definition term186 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := exists y0 : a0 -> a0, forall y1 : a0, (fun y2 : a0 => fun y3 : a0 => ((int_lt (x0 y3) (x0 y2)) /\ (~ (x1 y3))) \/ (x1 y2)) y1 (y0 y1).
Definition term184 (a0 : Type') (x0 : type1402 a0) := exists y0 : a0 -> a0, forall y1 : a0, x0 y1 (y0 y1).
Definition term182 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term100 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := imp (forall y0 : nat, forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1).
Definition term222 (x0 : int) (x1 : int) := ~ (int_lt x0 x1).
Definition term66 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (int_lt y0 (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1.
Definition term334 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term320 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) (x4 : a0) := ((int_le (int_of_num (NUMERAL 0)) x2) /\ ((int_lt x2 (x1 x0)) /\ ((x1 x4) = x2))) -> x3 x4.
Definition term64 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : int) (x3 : a0 -> Prop) := (int_le (int_of_num (NUMERAL 0)) x2) -> (int_lt x2 (int_of_num x0)) -> forall y0 : a0, ((x1 y0) = x2) -> x3 y0.
Definition term149 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := ~ (forall y0 : a0, (int_lt (x0 y0) (x0 x1)) -> x2 y0).
Definition term401 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0 -> int, (forall y3 : a0, int_le (int_of_num (NUMERAL 0)) (y2 y3)) -> (forall y3 : a0, (forall y4 : a0, (int_lt (y2 y4) (y2 y3)) -> y1 y4) -> y1 y3) -> (~ ((forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) -> forall y4 : a0, ((y2 y4) = y3) -> y1 y4) -> y1 y0)) -> False) x0.
Definition term381 (a0 : Type') (x0 : a0 -> int) (x1 : a0) := ~ ((x0 x1) = (x0 x1)).
Definition term257 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => ((int_lt (x0 (x1 y0)) (x0 y0)) \/ (x2 y0)) /\ ((~ (x2 (x1 y0))) \/ (x2 y0))) x3.
Definition term157 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : a0 -> Prop) := or (exists y0 : a0, (int_lt (x0 y0) (x0 x1)) /\ (~ (x2 y0))).
Definition term317 (a0 : Type') (x0 : a0) (x1 : a0 -> int) (x2 : a0) (x3 : int) := (int_le (int_of_num (NUMERAL 0)) x3) /\ ((int_lt x3 (x1 x0)) /\ ((x1 x2) = x3)).
Definition term268 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> a0) (x2 : a0) := ~ (int_le (int_of_num (NUMERAL 0)) (x0 (x1 x2))).
Definition term26 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) := fun y0 : nat => forall y1 : a0, ((x0 y1) = (int_of_num y0)) -> x1 y1.
Definition term178 (a0 : Type') (x0 : a0 -> int) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, ((int_lt (x0 y0) (x0 x2)) /\ (~ (x1 y0))) \/ (x1 x2).
Definition term18 (x0 : nat -> Prop) := forall y0 : nat, x0 y0.
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (int_lt (int_of_num y0) (int_of_num y1)).
Definition term55 (a0 : Type') (x0 : nat) (x1 : a0 -> int) (x2 : a0 -> Prop) := fun y0 : int => (int_lt y0 (int_of_num x0)) -> forall y1 : a0, ((x1 y1) = y0) -> x2 y1.
Definition term271 (x0 : Prop) := x0 -> ~ x0.
Definition term390 (a0 : Type') (x0 : a0 -> int) (x1 : a0) (x2 : int) := (~ ((x0 x1) = x2)) \/ (~ (int_le (int_of_num (NUMERAL 0)) x2)).
Definition term294 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term217 (a0 : Type') (x0 : int) (x1 : a0 -> int) (x2 : a0 -> Prop) := forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 x0)) \/ (forall y1 : a0, (~ ((x1 y1) = y0)) \/ (x2 y1))).
