Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term51 (x0 : int -> Prop) (x1 : int) := ~ ((fun y0 : int => x0 (int_abs y0)) x1).
Definition term258 (x0 : int) (x1 : int -> Prop) (x2 : int) := ~ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term200 (x0 : int) := (fun y0 : int => (~ ((int_abs y0) = y0)) \/ (int_le (int_of_num (NUMERAL 0)) y0)) x0.
Definition term68 (x0 : int -> Prop) := ~ ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0) = (forall y0 : int, x0 (int_abs y0))).
Definition term38 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term69 (x0 : type925) := ~ (all x0).
Definition term37 (x0 : int -> Prop) := ~ (all x0).
Definition term234 := (~ False) -> False.
Definition term85 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1)))) x0.
Definition term98 := exists y0 : int -> Prop, (fun y1 : int -> Prop => (exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y2 : int, y1 (int_abs y2))) y0.
Definition term93 := exists y0 : int -> Prop, (fun y1 : int -> Prop => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y1 y2)) /\ (exists y2 : int, ~ (y1 (int_abs y2)))) y0.
Definition term198 (x0 : int) := and ((fun y0 : int => ((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))) x0).
Definition term247 (x0 : int) (x1 : int -> Prop) (x2 : int) := (x1 x0) \/ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term230 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term268 (x0 : int -> Prop) (x1 : int) := ((int_abs x1) = x1) /\ (x0 (int_abs x1)).
Definition term238 (x0 : int) (x1 : int -> Prop) (x2 : int) := (x2 = x0) -> (x1 x0) \/ (~ (x1 x2)).
Definition term184 := exists y0 : int -> Prop, exists y1 : int, ((forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) \/ (((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2))).
Definition term140 := exists y0 : int -> Prop, exists y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2)).
Definition term118 := exists y0 : int -> Prop, exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1))).
Definition term181 (x0 : int -> Prop) := @eq Prop ((fun y0 : Prop => y0 = (exists y1 : int, ((forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) \/ (((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) /\ (forall y2 : int, x0 (int_abs y2))))) ((exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) \/ (exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1))))).
Definition term227 (x0 : Prop) := ~ (~ x0).
Definition term71 := exists y0 : int -> Prop, ~ ((fun y1 : int -> Prop => (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> y1 y2) = (forall y2 : int, y1 (int_abs y2))) y0).
Definition term194 := fun y0 : int => ((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term259 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ (~ (x2 = x0))) /\ (~ (~ (x1 x2))).
Definition term153 (x0 : int -> Prop) := or ((fun y0 : int -> Prop => exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) x0).
Definition term160 (x0 : int -> Prop) (x1 : int -> Prop) := (exists y0 : int, x0 y0) \/ (exists y0 : int, x1 y0).
Definition term250 (x0 : int -> Prop) (x1 : int) (x2 : int) := (~ (x0 x1)) \/ (~ (x1 = x2)).
Definition term12 := ~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1))).
Definition term59 (x0 : int -> Prop) := (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y0 : int, x0 (int_abs y0)).
Definition term72 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1))) x0.
Definition term0 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1)) x0.
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term262 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term21 := (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False.
Definition term270 (x0 : int -> Prop) (x1 : int) := (~ (x0 x1)) -> x0 x1.
Definition term100 := (exists y0 : int -> Prop, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1)))) \/ (exists y0 : int -> Prop, (exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y1 : int, y0 (int_abs y1))).
Definition term102 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term10 (x0 : Prop) := (~ x0) -> False.
Definition term251 (x0 : int -> Prop) (x1 : int) := or (x0 x1).
Definition term206 := fun y0 : int => (fun y1 : int => ((int_abs y1) = y1) \/ (~ (int_le (int_of_num (NUMERAL 0)) y1))) y0.
Definition term187 := forall y0 : int, (((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))) /\ ((~ ((int_abs y0) = y0)) \/ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term123 (x0 : int -> Prop) (x1 : Prop) := exists y0 : int, (x0 y0) /\ x1.
Definition term43 (x0 : int -> Prop) := fun y0 : int => ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> x0 y1) y0).
Definition term48 (x0 : int -> Prop) := ~ (forall y0 : int, x0 (int_abs y0)).
Definition term180 (x0 : int -> Prop) := (fun y0 : Prop => y0 = (exists y1 : int, ((forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) \/ (((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) /\ (forall y2 : int, x0 (int_abs y2))))) ((exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) \/ (exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1)))).
Definition term138 (x0 : int -> Prop) := exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1)).
Definition term58 (x0 : int -> Prop) := (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0)) /\ (forall y0 : int, x0 (int_abs y0)).
Definition term193 := (forall y0 : int, (fun y1 : int => ((int_abs y1) = y1) \/ (~ (int_le (int_of_num (NUMERAL 0)) y1))) y0) /\ (forall y0 : int, (fun y1 : int => (~ ((int_abs y1) = y1)) \/ (int_le (int_of_num (NUMERAL 0)) y1)) y0).
Definition term225 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term3 (x0 : int -> Prop) := @eq Prop (forall y0 : nat, x0 (int_of_num y0)).
Definition term119 := or (exists y0 : int -> Prop, exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))).
Definition term214 := (forall y0 : int, ((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))) /\ (forall y0 : int, (~ ((int_abs y0) = y0)) \/ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term99 := exists y0 : int -> Prop, (exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y1 : int, y0 (int_abs y1)).
Definition term41 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0) x1.
Definition term101 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term215 (x0 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) (int_abs y0)) x0.
Definition term159 := exists y0 : int -> Prop, (exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) \/ (exists y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2))).
Definition term47 (x0 : int -> Prop) := forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0).
Definition term220 (x0 : Prop) := (~ x0) -> x0.
Definition term14 := ((~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False) -> (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False.
Definition term19 := forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0).
Definition term257 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term57 (x0 : int -> Prop) := and (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))).
Definition term173 (x0 : int -> Prop) (x1 : int) := or ((fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) x1).
Definition term222 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term66 (x0 : int -> Prop) := ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0) /\ (~ (forall y0 : int, x0 (int_abs y0)))) \/ ((~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0)) /\ (forall y0 : int, x0 (int_abs y0))).
Definition term126 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) x1.
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term195 := fun y0 : int => (~ ((int_abs y0) = y0)) \/ (int_le (int_of_num (NUMERAL 0)) y0).
Definition term133 (x0 : int -> Prop) (x1 : int) := and ((int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (x0 x1))).
Definition term228 (x0 : int) := ~ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term182 (x0 : int -> Prop) := @eq Prop (((exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) \/ (exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1)))) = (exists y0 : int, ((forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) \/ (((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1))))).
Definition term94 := exists y0 : int -> Prop, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1))).
Definition term246 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term24 := (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> ~ (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)).
Definition term155 (x0 : int -> Prop) := ((fun y0 : int -> Prop => exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) x0) \/ ((fun y0 : int -> Prop => exists y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2))) x0).
Definition term242 (x0 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))) -> (int_abs x0) = x0.
Definition term267 (x0 : int) (x1 : int -> Prop) (x2 : int) := ((x0 = x2) /\ (x1 x0)) -> x1 x2.
Definition term213 := forall y0 : int, (~ ((int_abs y0) = y0)) \/ (int_le (int_of_num (NUMERAL 0)) y0).
Definition term97 := fun y0 : int -> Prop => (fun y1 : int -> Prop => (exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y2 : int, y1 (int_abs y2))) y0.
Definition term92 := fun y0 : int -> Prop => (fun y1 : int -> Prop => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y1 y2)) /\ (exists y2 : int, ~ (y1 (int_abs y2)))) y0.
Definition term264 (x0 : int) (x1 : int -> Prop) (x2 : int) := (x2 = x0) /\ (x1 x2).
Definition term209 := and (forall y0 : int, (fun y1 : int => ((int_abs y1) = y1) \/ (~ (int_le (int_of_num (NUMERAL 0)) y1))) y0).
Definition term157 := fun y0 : int -> Prop => ((fun y1 : int -> Prop => exists y2 : int, (forall y3 : int, (~ (int_le (int_of_num (NUMERAL 0)) y3)) \/ (y1 y3)) /\ (~ (y1 (int_abs y2)))) y0) \/ ((fun y1 : int -> Prop => exists y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y3 : int, y1 (int_abs y3))) y0).
Definition term89 := fun y0 : int -> Prop => ((fun y1 : int -> Prop => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y1 y2)) /\ (exists y2 : int, ~ (y1 (int_abs y2)))) y0) \/ ((fun y1 : int -> Prop => (exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y2 : int, y1 (int_abs y2))) y0).
Definition term106 (x0 : int -> Prop) := exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ ((fun y1 : int => ~ (x0 (int_abs y1))) y0).
Definition term205 := @eq Prop (forall y0 : int, (((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))) /\ ((~ ((int_abs y0) = y0)) \/ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term204 := @eq Prop (forall y0 : int, ((fun y1 : int => ((int_abs y1) = y1) \/ (~ (int_le (int_of_num (NUMERAL 0)) y1))) y0) /\ ((fun y1 : int => (~ ((int_abs y1) = y1)) \/ (int_le (int_of_num (NUMERAL 0)) y1)) y0)).
Definition term4 (x0 : int -> Prop) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0).
Definition term265 (x0 : int) (x1 : int -> Prop) (x2 : int) := imp (~ ((~ (x2 = x0)) \/ (~ (x1 x2)))).
Definition term109 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => ~ (x0 (int_abs y1))) y0.
Definition term34 (x0 : int -> Prop) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> x0 x1).
Definition term107 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => ~ (x0 (int_abs y0))) x1.
Definition term86 (x0 : int -> Prop) := or ((fun y0 : int -> Prop => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1)))) x0).
Definition term216 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) x1.
Definition term178 (x0 : int -> Prop) := fun y0 : int => ((forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) \/ (((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1))).
Definition term32 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> x0 x1.
Definition term9 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)).
Definition term8 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, y0 (int_abs y1)).
Definition term150 := exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y3 : int, y1 (int_abs y3))) y0.
Definition term146 := exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, (forall y3 : int, (~ (int_le (int_of_num (NUMERAL 0)) y3)) \/ (y1 y3)) /\ (~ (y1 (int_abs y2)))) y0.
Definition term65 (x0 : int -> Prop) := or ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ (exists y0 : int, ~ (x0 (int_abs y0)))).
Definition term237 (x0 : int) (x1 : int -> Prop) (x2 : int) := (x1 x0) \/ (~ (x1 x2)).
Definition term105 (x0 : int -> Prop) := (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ (exists y0 : int, (fun y1 : int => ~ (x0 (int_abs y1))) y0).
Definition term162 (x0 : int -> Prop) := (exists y0 : int, (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) y0) \/ (exists y0 : int, (fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) /\ (forall y2 : int, x0 (int_abs y2))) y0).
Definition term149 := fun y0 : int -> Prop => (fun y1 : int -> Prop => exists y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y3 : int, y1 (int_abs y3))) y0.
Definition term145 := fun y0 : int -> Prop => (fun y1 : int -> Prop => exists y2 : int, (forall y3 : int, (~ (int_le (int_of_num (NUMERAL 0)) y3)) \/ (y1 y3)) /\ (~ (y1 (int_abs y2)))) y0.
Definition term141 := (exists y0 : int -> Prop, exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) \/ (exists y0 : int -> Prop, exists y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2))).
Definition term50 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => x0 (int_abs y0)) x1.
Definition term218 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) (int_abs x0))) -> int_le (int_of_num (NUMERAL 0)) (int_abs x0).
Definition term116 (x0 : int -> Prop) := exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0))).
Definition term165 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) y0.
Definition term127 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) y0.
Definition term29 := forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0).
Definition term22 := (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> ~ (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)).
Definition term231 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (int_abs x1)) -> x0 (int_abs x1).
Definition term192 := forall y0 : int, ((fun y1 : int => ((int_abs y1) = y1) \/ (~ (int_le (int_of_num (NUMERAL 0)) y1))) y0) /\ ((fun y1 : int => (~ ((int_abs y1) = y1)) \/ (int_le (int_of_num (NUMERAL 0)) y1)) y0).
Definition term7 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)).
Definition term6 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, y0 (int_abs y1)).
Definition term256 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term35 (x0 : int -> Prop) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (x0 x1)).
Definition term45 (x0 : int -> Prop) := exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0)).
Definition term156 (x0 : int -> Prop) := (exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) \/ (exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1))).
Definition term142 := (exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, (forall y3 : int, (~ (int_le (int_of_num (NUMERAL 0)) y3)) \/ (y1 y3)) /\ (~ (y1 (int_abs y2)))) y0) \/ (exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y3 : int, y1 (int_abs y3))) y0).
Definition term82 := (exists y0 : int -> Prop, (fun y1 : int -> Prop => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y1 y2)) /\ (exists y2 : int, ~ (y1 (int_abs y2)))) y0) \/ (exists y0 : int -> Prop, (fun y1 : int -> Prop => (exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y2 : int, y1 (int_abs y2))) y0).
Definition term67 (x0 : int -> Prop) := ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ (exists y0 : int, ~ (x0 (int_abs y0)))) \/ ((exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y0 : int, x0 (int_abs y0))).
Definition term197 (x0 : int) := ((int_abs x0) = x0) \/ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term39 (x0 : int -> Prop) := ~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0).
Definition term18 := ~ (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)).
Definition term104 (x0 : Prop) (x1 : int -> Prop) := exists y0 : int, x0 /\ (x1 y0).
Definition term87 (x0 : int -> Prop) := (fun y0 : int -> Prop => (exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y1 : int, y0 (int_abs y1))) x0.
Definition term15 := (((~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False) -> (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False) -> (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False.
Definition term170 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) /\ (forall y2 : int, x0 (int_abs y2))) y0.
Definition term166 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) y0.
Definition term128 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) y0.
Definition term80 (x0 : type925) (x1 : type925) := (exists y0 : int -> Prop, x0 y0) \/ (exists y0 : int -> Prop, x1 y0).
Definition term2 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term245 (x0 : int) := ~ ((int_abs x0) = x0).
Definition term243 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_abs x0) = x0.
Definition term75 := fun y0 : int -> Prop => ((forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1)))) \/ ((exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y1 : int, y0 (int_abs y1))).
Definition term168 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1))) x1.
Definition term253 (x0 : int) (x1 : int -> Prop) (x2 : int) := @eq Prop ((~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2)))).
Definition term17 := (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False.
Definition term244 (x0 : int) := (~ ((int_abs x0) = x0)) -> (int_abs x0) = x0.
Definition term201 (x0 : int) := (~ ((int_abs x0) = x0)) \/ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term76 := exists y0 : int -> Prop, ((forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1)))) \/ ((exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y1 : int, y0 (int_abs y1))).
Definition term113 (x0 : int -> Prop) (x1 : int) := (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ (~ (x0 (int_abs x1))).
Definition term202 (x0 : int) := ((fun y0 : int => ((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))) x0) /\ ((fun y0 : int => (~ ((int_abs y0) = y0)) \/ (int_le (int_of_num (NUMERAL 0)) y0)) x0).
Definition term203 := fun y0 : int => ((fun y1 : int => ((int_abs y1) = y1) \/ (~ (int_le (int_of_num (NUMERAL 0)) y1))) y0) /\ ((fun y1 : int => (~ ((int_abs y1) = y1)) \/ (int_le (int_of_num (NUMERAL 0)) y1)) y0).
Definition term240 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2))).
Definition term185 (x0 : int) := (((int_abs x0) = x0) \/ (~ (int_le (int_of_num (NUMERAL 0)) x0))) /\ ((~ ((int_abs x0) = x0)) \/ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term223 (x0 : int -> Prop) (x1 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (x0 x1)).
Definition term11 := (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> False.
Definition term219 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) (int_abs x0)).
Definition term183 := fun y0 : int -> Prop => exists y1 : int, ((forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) \/ (((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2))).
Definition term139 := fun y0 : int -> Prop => exists y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2)).
Definition term117 := fun y0 : int -> Prop => exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1))).
Definition term217 (x0 : int -> Prop) (x1 : int) := ~ (x0 x1).
Definition term83 := fun y0 : int -> Prop => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1))).
Definition term79 (x0 : type925) (x1 : type925) := exists y0 : int -> Prop, (x0 y0) \/ (x1 y0).
Definition term177 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) y0) \/ ((fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) /\ (forall y2 : int, x0 (int_abs y2))) y0).
Definition term263 (x0 : int -> Prop) (x1 : int) := ~ (~ (x0 x1)).
Definition term125 (x0 : int -> Prop) := exists y0 : int, ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) y0) /\ (forall y1 : int, x0 (int_abs y1)).
Definition term16 := (((~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False) -> (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False) -> ((~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False) -> (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False.
Definition term55 (x0 : int -> Prop) := exists y0 : int, ~ (x0 (int_abs y0)).
Definition term53 (x0 : int -> Prop) := fun y0 : int => ~ ((fun y1 : int => x0 (int_abs y1)) y0).
Definition term261 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term124 (x0 : int -> Prop) := (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) y0) /\ (forall y0 : int, x0 (int_abs y0)).
Definition term114 (x0 : int -> Prop) := fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ ((fun y1 : int => ~ (x0 (int_abs y1))) y0).
Definition term129 (x0 : int -> Prop) := and (exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) y0).
Definition term179 (x0 : int -> Prop) := exists y0 : int, ((forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) \/ (((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1))).
Definition term132 (x0 : int -> Prop) (x1 : int) := and ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) x1).
Definition term235 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term248 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term42 (x0 : int -> Prop) (x1 : int) := ~ ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0) x1).
Definition term224 (x0 : int -> Prop) (x1 : int) := @eq Prop ((x0 x1) \/ (~ (int_le (int_of_num (NUMERAL 0)) x1))).
Definition term169 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) /\ (forall y2 : int, x0 (int_abs y2))) y0.
Definition term90 := @eq Prop (exists y0 : int -> Prop, ((fun y1 : int -> Prop => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y1 y2)) /\ (exists y2 : int, ~ (y1 (int_abs y2)))) y0) \/ ((fun y1 : int -> Prop => (exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y2 : int, y1 (int_abs y2))) y0)).
Definition term190 (x0 : int -> Prop) (x1 : int -> Prop) := forall y0 : int, (x0 y0) /\ (x1 y0).
Definition term254 (x0 : int -> Prop) (x1 : int) (x2 : int) := @eq Prop ((x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2)))).
Definition term122 (x0 : int -> Prop) (x1 : Prop) := (exists y0 : int, x0 y0) /\ x1.
Definition term84 := fun y0 : int -> Prop => (exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y1 : int, y0 (int_abs y1)).
Definition term137 (x0 : int -> Prop) := fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1)).
Definition term108 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => ~ (x0 (int_abs y1))) y0.
Definition term196 (x0 : int) := (fun y0 : int => ((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))) x0.
Definition term210 := and (forall y0 : int, ((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))).
Definition term61 (x0 : int -> Prop) := and (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)).
Definition term60 (x0 : int -> Prop) := and (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0).
Definition term1 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term30 (x0 : int -> Prop) (x1 : int) := x0 (int_abs x1).
Definition term161 (x0 : int -> Prop) (x1 : int -> Prop) := exists y0 : int, (x0 y0) \/ (x1 y0).
Definition term25 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_abs x0).
Definition term175 (x0 : int -> Prop) (x1 : int) := ((fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) x1) \/ ((fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1))) x1).
Definition term147 := or (exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, (forall y3 : int, (~ (int_le (int_of_num (NUMERAL 0)) y3)) \/ (y1 y3)) /\ (~ (y1 (int_abs y2)))) y0).
Definition term95 := or (exists y0 : int -> Prop, (fun y1 : int -> Prop => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y1 y2)) /\ (exists y2 : int, ~ (y1 (int_abs y2)))) y0).
Definition term208 := forall y0 : int, ((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term33 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term211 := fun y0 : int => (fun y1 : int => (~ ((int_abs y1) = y1)) \/ (int_le (int_of_num (NUMERAL 0)) y1)) y0.
Definition term176 (x0 : int) (x1 : int -> Prop) := ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x1 y0)) /\ (~ (x1 (int_abs x0)))) \/ (((int_le (int_of_num (NUMERAL 0)) x0) /\ (~ (x1 x0))) /\ (forall y0 : int, x1 (int_abs y0))).
Definition term54 (x0 : int -> Prop) := fun y0 : int => ~ (x0 (int_abs y0)).
Definition term64 (x0 : int -> Prop) := or ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0) /\ (~ (forall y0 : int, x0 (int_abs y0)))).
Definition term255 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ ((~ (x0 = x2)) \/ (~ (x1 x0)))) -> x1 x2.
Definition term44 (x0 : int -> Prop) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0)).
Definition term199 (x0 : int) := and (((int_abs x0) = x0) \/ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term174 (x0 : int -> Prop) (x1 : int) := or ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ (~ (x0 (int_abs x1)))).
Definition term136 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) y0) /\ (forall y1 : int, x0 (int_abs y1)).
Definition term154 (x0 : int -> Prop) := or (exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))).
Definition term46 (x0 : int -> Prop) := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0).
Definition term191 (x0 : int -> Prop) (x1 : int -> Prop) := (forall y0 : int, x0 y0) /\ (forall y0 : int, x1 y0).
Definition term232 (x0 : int -> Prop) (x1 : int) := (~ (x0 (int_abs x1))) -> x0 (int_abs x1).
Definition term52 (x0 : int -> Prop) (x1 : int) := ~ (x0 (int_abs x1)).
Definition term163 (x0 : int -> Prop) := exists y0 : int, ((fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) y0) \/ ((fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) /\ (forall y2 : int, x0 (int_abs y2))) y0).
Definition term28 := fun y0 : int => ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0).
Definition term31 (x0 : int -> Prop) := fun y0 : int => x0 (int_abs y0).
Definition term143 := exists y0 : int -> Prop, ((fun y1 : int -> Prop => exists y2 : int, (forall y3 : int, (~ (int_le (int_of_num (NUMERAL 0)) y3)) \/ (y1 y3)) /\ (~ (y1 (int_abs y2)))) y0) \/ ((fun y1 : int -> Prop => exists y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y3 : int, y1 (int_abs y3))) y0).
Definition term81 := exists y0 : int -> Prop, ((fun y1 : int -> Prop => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y1 y2)) /\ (exists y2 : int, ~ (y1 (int_abs y2)))) y0) \/ ((fun y1 : int -> Prop => (exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y2 : int, y1 (int_abs y2))) y0).
Definition term158 := fun y0 : int -> Prop => (exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) \/ (exists y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2))).
Definition term226 (x0 : int -> Prop) (x1 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> x0 x1.
Definition term239 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term271 (x0 : int -> Prop) (x1 : int) := (x0 x1) -> False.
Definition term91 := @eq Prop (exists y0 : int -> Prop, ((forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1)))) \/ ((exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y1 : int, y0 (int_abs y1)))).
Definition term269 (x0 : int -> Prop) (x1 : int) := (((int_abs x1) = x1) /\ (x0 (int_abs x1))) -> x0 x1.
Definition term112 (x0 : int -> Prop) (x1 : int) := (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ ((fun y0 : int => ~ (x0 (int_abs y0))) x1).
Definition term5 (x0 : int -> Prop) := forall y0 : int, x0 (int_abs y0).
Definition term56 (x0 : int -> Prop) := and (~ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0)).
Definition term111 (x0 : int -> Prop) := @eq Prop ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ (exists y0 : int, ~ (x0 (int_abs y0)))).
Definition term110 (x0 : int -> Prop) := @eq Prop ((forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ (exists y0 : int, (fun y1 : int => ~ (x0 (int_abs y1))) y0)).
Definition term167 (x0 : int -> Prop) := or (exists y0 : int, (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) y0).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term74 := fun y0 : int -> Prop => ~ ((fun y1 : int -> Prop => (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> y1 y2) = (forall y2 : int, y1 (int_abs y2))) y0).
Definition term49 (x0 : int -> Prop) := exists y0 : int, ~ ((fun y1 : int => x0 (int_abs y1)) y0).
Definition term40 (x0 : int -> Prop) := exists y0 : int, ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> x0 y1) y0).
Definition term103 (x0 : Prop) (x1 : int -> Prop) := x0 /\ (exists y0 : int, x1 y0).
Definition term164 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) x1.
Definition term70 (x0 : type925) := exists y0 : int -> Prop, ~ (x0 y0).
Definition term131 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y0 : int, x0 (int_abs y0))).
Definition term130 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) y0) /\ (forall y0 : int, x0 (int_abs y0))).
Definition term36 (x0 : int -> Prop) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (x0 x1).
Definition term134 (x0 : int) (x1 : int -> Prop) := ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x1 y0))) x0) /\ (forall y0 : int, x1 (int_abs y0)).
Definition term233 (x0 : int -> Prop) (x1 : int) := (x0 (int_abs x1)) -> False.
Definition term27 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term135 (x0 : int) (x1 : int -> Prop) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (~ (x1 x0))) /\ (forall y0 : int, x1 (int_abs y0)).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term20 := imp (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term249 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ (x2 = x0)) \/ (~ (x1 x2)).
Definition term260 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term96 := or (exists y0 : int -> Prop, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1)))).
Definition term73 (x0 : int -> Prop) := ~ ((fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1))) x0).
Definition term148 (x0 : int -> Prop) := (fun y0 : int -> Prop => exists y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2))) x0.
Definition term144 (x0 : int -> Prop) := (fun y0 : int -> Prop => exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) x0.
Definition term62 (x0 : int -> Prop) := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0) /\ (~ (forall y0 : int, x0 (int_abs y0))).
Definition term252 (x0 : int -> Prop) (x1 : int) (x2 : int) := (x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2))).
Definition term88 (x0 : int -> Prop) := ((fun y0 : int -> Prop => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (y0 y1)) /\ (exists y1 : int, ~ (y0 (int_abs y1)))) x0) \/ ((fun y0 : int -> Prop => (exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y1 : int, y0 (int_abs y1))) x0).
Definition term63 (x0 : int -> Prop) := (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (x0 y0)) /\ (exists y0 : int, ~ (x0 (int_abs y0))).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term266 (x0 : int) (x1 : int -> Prop) (x2 : int) := imp ((x2 = x0) /\ (x1 x2)).
Definition term13 := (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))) -> (forall y0 : int, ((int_abs y0) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) -> (forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_abs y0)) -> False.
Definition term212 := forall y0 : int, (fun y1 : int => (~ ((int_abs y1) = y1)) \/ (int_le (int_of_num (NUMERAL 0)) y1)) y0.
Definition term207 := forall y0 : int, (fun y1 : int => ((int_abs y1) = y1) \/ (~ (int_le (int_of_num (NUMERAL 0)) y1))) y0.
Definition term221 (x0 : int -> Prop) (x1 : int) := (x0 x1) \/ (~ (int_le (int_of_num (NUMERAL 0)) x1)).
Definition term186 := fun y0 : int => (((int_abs y0) = y0) \/ (~ (int_le (int_of_num (NUMERAL 0)) y0))) /\ ((~ ((int_abs y0) = y0)) \/ (int_le (int_of_num (NUMERAL 0)) y0)).
Definition term241 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term26 := fun y0 : int => int_le (int_of_num (NUMERAL 0)) (int_abs y0).
Definition term236 (x0 : int) (x1 : int -> Prop) (x2 : int) := ((x1 x2) = (x1 x0)) -> (x1 x0) \/ (~ (x1 x2)).
Definition term23 := imp (~ (forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : int, y0 (int_abs y1)))).
Definition term229 (x0 : int) := imp (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term115 (x0 : int -> Prop) := fun y0 : int => (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0))).
Definition term172 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (x0 y1)) /\ (~ (x0 (int_abs y0)))) \/ (exists y0 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (~ (x0 y0))) /\ (forall y1 : int, x0 (int_abs y1)))).
Definition term171 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (fun y1 : int => (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (x0 y2)) /\ (~ (x0 (int_abs y1)))) y0) \/ (exists y0 : int, (fun y1 : int => ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (x0 y1))) /\ (forall y2 : int, x0 (int_abs y2))) y0)).
Definition term152 := @eq Prop ((exists y0 : int -> Prop, exists y1 : int, (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (y0 y2)) /\ (~ (y0 (int_abs y1)))) \/ (exists y0 : int -> Prop, exists y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (~ (y0 y1))) /\ (forall y2 : int, y0 (int_abs y2)))).
Definition term151 := @eq Prop ((exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, (forall y3 : int, (~ (int_le (int_of_num (NUMERAL 0)) y3)) \/ (y1 y3)) /\ (~ (y1 (int_abs y2)))) y0) \/ (exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (~ (y1 y2))) /\ (forall y3 : int, y1 (int_abs y3))) y0)).
