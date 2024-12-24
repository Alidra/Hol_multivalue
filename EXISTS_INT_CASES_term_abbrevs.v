Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term94 (x0 : int -> Prop) := or ((fun y0 : int -> Prop => (exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1)))))) x0).
Definition term21 (x0 : int -> Prop) (x1 : nat) := x0 (int_neg (int_of_num x1)).
Definition term311 (x0 : int) (x1 : int -> Prop) (x2 : int) := ~ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term77 (x0 : type925) := ~ (all x0).
Definition term327 := (~ False) -> False.
Definition term4 := (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False.
Definition term81 (x0 : int -> Prop) := ~ ((fun y0 : int -> Prop => (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1))))) x0).
Definition term106 := exists y0 : int -> Prop, (fun y1 : int -> Prop => (forall y2 : int, ~ (y1 y2)) /\ ((exists y2 : nat, y1 (int_of_num y2)) \/ (exists y2 : nat, y1 (int_neg (int_of_num y2))))) y0.
Definition term101 := exists y0 : int -> Prop, (fun y1 : int -> Prop => (exists y2 : int, y1 y2) /\ ((forall y2 : nat, ~ (y1 (int_of_num y2))) /\ (forall y2 : nat, ~ (y1 (int_neg (int_of_num y2)))))) y0.
Definition term179 (x0 : int -> Prop) := fun y0 : int => (x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1))))).
Definition term66 (x0 : int -> Prop) := and (forall y0 : int, ~ (x0 y0)).
Definition term303 (x0 : int) (x1 : int -> Prop) (x2 : int) := (x1 x0) \/ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term225 (x0 : int) (x1 : nat) := or ((fun y0 : nat => x0 = (int_of_num y0)) x1).
Definition term252 (x0 : int -> nat) := fun y0 : int => (fun y1 : int => fun y2 : nat => (y1 = (int_of_num y2)) \/ (y1 = (int_neg (int_of_num y2)))) y0 (x0 y0).
Definition term267 (x0 : int) (x1 : int -> Prop) (x2 : int) := (x2 = x0) -> (x1 x0) \/ (~ (x1 x2)).
Definition term153 := exists y0 : int -> Prop, exists y1 : nat, (forall y2 : int, ~ (y0 y2)) /\ ((y0 (int_of_num y1)) \/ (y0 (int_neg (int_of_num y1)))).
Definition term115 := exists y0 : int -> Prop, exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2))))).
Definition term193 (x0 : int -> Prop) := exists y0 : int, ((x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1)))))) \/ (exists y1 : nat, (forall y2 : int, ~ (x0 y2)) /\ ((x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1))))).
Definition term83 := fun y0 : int -> Prop => ((exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1)))))) \/ ((forall y1 : int, ~ (y0 y1)) /\ ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1))))).
Definition term283 (x0 : Prop) := ~ (~ x0).
Definition term79 := exists y0 : int -> Prop, ~ ((fun y1 : int -> Prop => (exists y2 : int, y1 y2) = ((exists y2 : nat, y1 (int_of_num y2)) \/ (exists y2 : nat, y1 (int_neg (int_of_num y2))))) y0).
Definition term312 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ (~ (x2 = x0))) /\ (~ (~ (x1 x2))).
Definition term166 (x0 : int -> Prop) := or ((fun y0 : int -> Prop => exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2)))))) x0).
Definition term177 (x0 : int -> Prop) := (exists y0 : int, (fun y1 : int => (x0 y1) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) y0) \/ (exists y0 : nat, (forall y1 : int, ~ (x0 y1)) /\ ((x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0))))).
Definition term245 (x0 : int) := exists y0 : nat, (fun y1 : int => fun y2 : nat => (y1 = (int_of_num y2)) \/ (y1 = (int_neg (int_of_num y2)))) x0 y0.
Definition term232 := fun y0 : int => exists y1 : nat, (y0 = (int_of_num y1)) \/ (y0 = (int_neg (int_of_num y1))).
Definition term210 (x0 : int -> Prop) := fun y0 : int => exists y1 : nat, ((x0 y0) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) \/ ((forall y2 : int, ~ (x0 y2)) /\ ((x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1))))).
Definition term65 (x0 : int -> Prop) := and (~ (exists y0 : int, x0 y0)).
Definition term60 (x0 : int -> Prop) := and (~ (exists y0 : nat, x0 (int_of_num y0))).
Definition term18 (x0 : int) := or (exists y0 : nat, x0 = (int_of_num y0)).
Definition term289 (x0 : int -> Prop) (x1 : int) (x2 : int) := ((~ (x0 x2)) /\ (x0 x1)) -> ~ (x1 = x2).
Definition term305 (x0 : int -> Prop) (x1 : int) (x2 : int) := (~ (x0 x1)) \/ (~ (x1 = x2)).
Definition term178 (x0 : int -> Prop) := exists y0 : int, ((fun y1 : int => (x0 y1) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) y0) \/ (exists y1 : nat, (forall y2 : int, ~ (x0 y2)) /\ ((x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1))))).
Definition term169 (x0 : int -> Prop) := (exists y0 : int, (x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1)))))) \/ (exists y0 : nat, (forall y1 : int, ~ (x0 y1)) /\ ((x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0))))).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term19 (x0 : int) := (exists y0 : nat, x0 = (int_of_num y0)) \/ (exists y0 : nat, x0 = (int_neg (int_of_num y0))).
Definition term244 (x0 : int) := fun y0 : nat => (fun y1 : int => fun y2 : nat => (y1 = (int_of_num y2)) \/ (y1 = (int_neg (int_of_num y2)))) x0 y0.
Definition term73 (x0 : int -> Prop) := or ((exists y0 : int, x0 y0) /\ ((forall y0 : nat, ~ (x0 (int_of_num y0))) /\ (forall y0 : nat, ~ (x0 (int_neg (int_of_num y0)))))).
Definition term328 (x0 : int -> Prop) (x1 : nat) := (~ (x0 (int_of_num x1))) -> x0 (int_of_num x1).
Definition term315 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term243 (x0 : int) (x1 : nat) := (fun y0 : nat => (x0 = (int_of_num y0)) \/ (x0 = (int_neg (int_of_num y0)))) x1.
Definition term274 (x0 : int -> Prop) (x1 : int) := (~ (x0 x1)) -> x0 x1.
Definition term137 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term1 := forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term306 (x0 : int -> Prop) (x1 : int) := or (x0 x1).
Definition term112 (x0 : int -> Prop) (x1 : Prop) := exists y0 : int, (x0 y0) /\ x1.
Definition term23 (x0 : int -> Prop) := exists y0 : nat, x0 (int_neg (int_of_num y0)).
Definition term74 (x0 : int -> Prop) := ((exists y0 : int, x0 y0) /\ (~ ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0)))))) \/ ((~ (exists y0 : int, x0 y0)) /\ ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0))))).
Definition term41 (x0 : int -> Prop) := fun y0 : int => ~ (x0 y0).
Definition term148 (x0 : int -> Prop) (x1 : nat) := (forall y0 : int, ~ (x0 y0)) /\ ((x0 (int_of_num x1)) \/ (x0 (int_neg (int_of_num x1)))).
Definition term40 (x0 : int -> Prop) := fun y0 : int => ~ ((fun y1 : int => x0 y1) y0).
Definition term63 (x0 : int -> Prop) := (forall y0 : nat, ~ (x0 (int_of_num y0))) /\ (forall y0 : nat, ~ (x0 (int_neg (int_of_num y0)))).
Definition term197 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term209 (x0 : int) (x1 : int -> Prop) := exists y0 : nat, ((x1 x0) /\ ((forall y1 : nat, ~ (x1 (int_of_num y1))) /\ (forall y1 : nat, ~ (x1 (int_neg (int_of_num y1)))))) \/ ((forall y1 : int, ~ (x1 y1)) /\ ((x1 (int_of_num y0)) \/ (x1 (int_neg (int_of_num y0))))).
Definition term262 (x0 : int -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 (int_neg (int_of_num y0)))) x1.
Definition term276 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term80 (x0 : int -> Prop) := (fun y0 : int -> Prop => (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term116 := or (exists y0 : int -> Prop, exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2)))))).
Definition term46 (x0 : int -> Prop) (x1 : nat) := (fun y0 : nat => x0 (int_of_num y0)) x1.
Definition term175 (x0 : int -> Prop) (x1 : Prop) := (exists y0 : int, x0 y0) \/ x1.
Definition term213 := exists y0 : int -> Prop, exists y1 : int, exists y2 : nat, ((y0 y1) /\ ((forall y3 : nat, ~ (y0 (int_of_num y3))) /\ (forall y3 : nat, ~ (y0 (int_neg (int_of_num y3)))))) \/ ((forall y3 : int, ~ (y0 y3)) /\ ((y0 (int_of_num y2)) \/ (y0 (int_neg (int_of_num y2))))).
Definition term136 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term76 (x0 : int -> Prop) := ~ ((exists y0 : int, x0 y0) = ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0))))).
Definition term61 (x0 : int -> Prop) := and (forall y0 : nat, ~ (x0 (int_of_num y0))).
Definition term263 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => ~ (x0 y0)) x1.
Definition term172 := exists y0 : int -> Prop, (exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2)))))) \/ (exists y1 : nat, (forall y2 : int, ~ (y0 y2)) /\ ((y0 (int_of_num y1)) \/ (y0 (int_neg (int_of_num y1))))).
Definition term288 (x0 : int) (x1 : int -> Prop) (x2 : int) := imp ((~ (x1 x0)) /\ (x1 x2)).
Definition term275 (x0 : Prop) := (~ x0) -> x0.
Definition term325 (x0 : int -> Prop) (x1 : nat) := (x0 (int_neg (int_of_num x1))) -> False.
Definition term220 (x0 : int) (x1 : nat) := (fun y0 : nat => x0 = (int_neg (int_of_num y0))) x1.
Definition term129 (x0 : int -> Prop) (x1 : nat) := or (x0 (int_of_num x1)).
Definition term212 := fun y0 : int -> Prop => exists y1 : int, exists y2 : nat, ((y0 y1) /\ ((forall y3 : nat, ~ (y0 (int_of_num y3))) /\ (forall y3 : nat, ~ (y0 (int_neg (int_of_num y3)))))) \/ ((forall y3 : int, ~ (y0 y3)) /\ ((y0 (int_of_num y2)) \/ (y0 (int_neg (int_of_num y2))))).
Definition term280 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term133 (x0 : int -> Prop) := fun y0 : nat => (x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0))).
Definition term26 (x0 : int -> Prop) := exists y0 : nat, x0 (int_of_num y0).
Definition term58 (x0 : int -> Prop) := fun y0 : nat => ~ (x0 (int_neg (int_of_num y0))).
Definition term234 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term187 (x0 : int -> Prop) (x1 : int) := or ((fun y0 : int => (x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1)))))) x1).
Definition term91 := fun y0 : int -> Prop => (exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1))))).
Definition term108 := (exists y0 : int -> Prop, (exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1)))))) \/ (exists y0 : int -> Prop, (forall y1 : int, ~ (y0 y1)) /\ ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1))))).
Definition term258 := exists y0 : int -> nat, forall y1 : int, (y1 = (int_of_num (y0 y1))) \/ (y1 = (int_neg (int_of_num (y0 y1)))).
Definition term239 := exists y0 : int -> nat, forall y1 : int, (fun y2 : int => fun y3 : nat => (y2 = (int_of_num y3)) \/ (y2 = (int_neg (int_of_num y3)))) y1 (y0 y1).
Definition term237 (x0 : type1552) := exists y0 : int -> nat, forall y1 : int, x0 y1 (y0 y1).
Definition term143 (x0 : int -> Prop) := fun y0 : nat => (fun y1 : nat => (x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1)))) y0.
Definition term140 (x0 : int -> Prop) := (forall y0 : int, ~ (x0 y0)) /\ (exists y0 : nat, (fun y1 : nat => (x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1)))) y0).
Definition term330 (x0 : int -> Prop) (x1 : nat) := (x0 (int_of_num x1)) -> False.
Definition term105 := fun y0 : int -> Prop => (fun y1 : int -> Prop => (forall y2 : int, ~ (y1 y2)) /\ ((exists y2 : nat, y1 (int_of_num y2)) \/ (exists y2 : nat, y1 (int_neg (int_of_num y2))))) y0.
Definition term100 := fun y0 : int -> Prop => (fun y1 : int -> Prop => (exists y2 : int, y1 y2) /\ ((forall y2 : nat, ~ (y1 (int_of_num y2))) /\ (forall y2 : nat, ~ (y1 (int_neg (int_of_num y2)))))) y0.
Definition term92 := fun y0 : int -> Prop => (forall y1 : int, ~ (y0 y1)) /\ ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))).
Definition term302 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term14 (x0 : int) := fun y0 : nat => x0 = (int_neg (int_of_num y0)).
Definition term31 (x0 : int -> Prop) := @eq Prop (exists y0 : int, x0 y0).
Definition term241 (x0 : int) := (fun y0 : int => fun y1 : nat => (y0 = (int_of_num y1)) \/ (y0 = (int_neg (int_of_num y1)))) x0.
Definition term50 (x0 : int -> Prop) := fun y0 : nat => ~ (x0 (int_of_num y0)).
Definition term322 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := x0 (int_neg (int_of_num (x1 x2))).
Definition term168 (x0 : int -> Prop) := ((fun y0 : int -> Prop => exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2)))))) x0) \/ ((fun y0 : int -> Prop => exists y1 : nat, (forall y2 : int, ~ (y0 y2)) /\ ((y0 (int_of_num y1)) \/ (y0 (int_neg (int_of_num y1))))) x0).
Definition term319 (x0 : int) (x1 : int -> Prop) (x2 : int) := ((x0 = x2) /\ (x1 x0)) -> x1 x2.
Definition term84 := exists y0 : int -> Prop, ((exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1)))))) \/ ((forall y1 : int, ~ (y0 y1)) /\ ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1))))).
Definition term20 := fun y0 : int => (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1))).
Definition term180 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => (x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1)))))) x1.
Definition term29 (x0 : int -> Prop) := fun y0 : int => x0 y0.
Definition term316 (x0 : int) (x1 : int -> Prop) (x2 : int) := (x2 = x0) /\ (x1 x2).
Definition term170 := fun y0 : int -> Prop => ((fun y1 : int -> Prop => exists y2 : int, (y1 y2) /\ ((forall y3 : nat, ~ (y1 (int_of_num y3))) /\ (forall y3 : nat, ~ (y1 (int_neg (int_of_num y3)))))) y0) \/ ((fun y1 : int -> Prop => exists y2 : nat, (forall y3 : int, ~ (y1 y3)) /\ ((y1 (int_of_num y2)) \/ (y1 (int_neg (int_of_num y2))))) y0).
Definition term97 := fun y0 : int -> Prop => ((fun y1 : int -> Prop => (exists y2 : int, y1 y2) /\ ((forall y2 : nat, ~ (y1 (int_of_num y2))) /\ (forall y2 : nat, ~ (y1 (int_neg (int_of_num y2)))))) y0) \/ ((fun y1 : int -> Prop => (forall y2 : int, ~ (y1 y2)) /\ ((exists y2 : nat, y1 (int_of_num y2)) \/ (exists y2 : nat, y1 (int_neg (int_of_num y2))))) y0).
Definition term139 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term38 (x0 : int -> Prop) (x1 : int) := ~ ((fun y0 : int => x0 y0) x1).
Definition term317 (x0 : int) (x1 : int -> Prop) (x2 : int) := imp (~ ((~ (x2 = x0)) \/ (~ (x1 x2)))).
Definition term52 (x0 : int -> Prop) := ~ (exists y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term44 (x0 : int -> Prop) := ~ (exists y0 : nat, x0 (int_of_num y0)).
Definition term34 (x0 : int -> Prop) := forall y0 : int, ~ (x0 y0).
Definition term124 (x0 : int -> Prop) := fun y0 : nat => (fun y1 : nat => x0 (int_neg (int_of_num y1))) y0.
Definition term121 (x0 : int -> Prop) := fun y0 : nat => (fun y1 : nat => x0 (int_of_num y1)) y0.
Definition term54 (x0 : int -> Prop) (x1 : nat) := (fun y0 : nat => x0 (int_neg (int_of_num y0))) x1.
Definition term138 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term285 (x0 : int -> Prop) (x1 : int) := and (~ (x0 x1)).
Definition term255 (x0 : int -> nat) := forall y0 : int, (y0 = (int_of_num (x0 y0))) \/ (y0 = (int_neg (int_of_num (x0 y0)))).
Definition term214 (x0 : int) := (exists y0 : nat, (fun y1 : nat => x0 = (int_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => x0 = (int_neg (int_of_num y1))) y0).
Definition term119 (x0 : int -> Prop) := (exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => x0 (int_neg (int_of_num y1))) y0).
Definition term128 (x0 : int -> Prop) (x1 : nat) := or ((fun y0 : nat => x0 (int_of_num y0)) x1).
Definition term321 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := ((x2 = (int_neg (int_of_num (x1 x2)))) /\ (x0 x2)) -> x0 (int_neg (int_of_num (x1 x2))).
Definition term300 (x0 : int -> nat) (x1 : int) := (~ (x1 = (int_neg (int_of_num (x0 x1))))) -> x1 = (int_neg (int_of_num (x0 x1))).
Definition term299 (x0 : int -> nat) (x1 : int) := (~ (x1 = (int_of_num (x0 x1)))) -> x1 = (int_neg (int_of_num (x0 x1))).
Definition term113 (x0 : int -> Prop) := exists y0 : int, (x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1))))).
Definition term216 (x0 : int) (x1 : nat) := (fun y0 : nat => x0 = (int_of_num y0)) x1.
Definition term3 := ~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1))))).
Definition term207 (x0 : int) (x1 : int -> Prop) := fun y0 : nat => ((x1 x0) /\ ((forall y1 : nat, ~ (x1 (int_of_num y1))) /\ (forall y1 : nat, ~ (x1 (int_neg (int_of_num y1)))))) \/ ((fun y1 : nat => (forall y2 : int, ~ (x1 y2)) /\ ((x1 (int_of_num y1)) \/ (x1 (int_neg (int_of_num y1))))) y0).
Definition term163 := exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : nat, (forall y3 : int, ~ (y1 y3)) /\ ((y1 (int_of_num y2)) \/ (y1 (int_neg (int_of_num y2))))) y0.
Definition term159 := exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, (y1 y2) /\ ((forall y3 : nat, ~ (y1 (int_of_num y3))) /\ (forall y3 : nat, ~ (y1 (int_neg (int_of_num y3)))))) y0.
Definition term150 (x0 : int -> Prop) := fun y0 : nat => (forall y1 : int, ~ (x0 y1)) /\ ((x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0)))).
Definition term266 (x0 : int) (x1 : int -> Prop) (x2 : int) := (x1 x0) \/ (~ (x1 x2)).
Definition term6 := (((~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False) -> (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False) -> (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False.
Definition term162 := fun y0 : int -> Prop => (fun y1 : int -> Prop => exists y2 : nat, (forall y3 : int, ~ (y1 y3)) /\ ((y1 (int_of_num y2)) \/ (y1 (int_neg (int_of_num y2))))) y0.
Definition term158 := fun y0 : int -> Prop => (fun y1 : int -> Prop => exists y2 : int, (y1 y2) /\ ((forall y3 : nat, ~ (y1 (int_of_num y3))) /\ (forall y3 : nat, ~ (y1 (int_neg (int_of_num y3)))))) y0.
Definition term154 := (exists y0 : int -> Prop, exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2)))))) \/ (exists y0 : int -> Prop, exists y1 : nat, (forall y2 : int, ~ (y0 y2)) /\ ((y0 (int_of_num y1)) \/ (y0 (int_neg (int_of_num y1))))).
Definition term195 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term22 (x0 : int -> Prop) := fun y0 : nat => x0 (int_neg (int_of_num y0)).
Definition term107 := exists y0 : int -> Prop, (forall y1 : int, ~ (y0 y1)) /\ ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))).
Definition term102 := exists y0 : int -> Prop, (exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1))))).
Definition term279 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term228 (x0 : int) (x1 : nat) := (x0 = (int_of_num x1)) \/ (x0 = (int_neg (int_of_num x1))).
Definition term206 (x0 : int) (x1 : int -> Prop) (x2 : nat) := ((x1 x0) /\ ((forall y0 : nat, ~ (x1 (int_of_num y0))) /\ (forall y0 : nat, ~ (x1 (int_neg (int_of_num y0)))))) \/ ((forall y0 : int, ~ (x1 y0)) /\ ((x1 (int_of_num x2)) \/ (x1 (int_neg (int_of_num x2))))).
Definition term155 := (exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, (y1 y2) /\ ((forall y3 : nat, ~ (y1 (int_of_num y3))) /\ (forall y3 : nat, ~ (y1 (int_neg (int_of_num y3)))))) y0) \/ (exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : nat, (forall y3 : int, ~ (y1 y3)) /\ ((y1 (int_of_num y2)) \/ (y1 (int_neg (int_of_num y2))))) y0).
Definition term90 := (exists y0 : int -> Prop, (fun y1 : int -> Prop => (exists y2 : int, y1 y2) /\ ((forall y2 : nat, ~ (y1 (int_of_num y2))) /\ (forall y2 : nat, ~ (y1 (int_neg (int_of_num y2)))))) y0) \/ (exists y0 : int -> Prop, (fun y1 : int -> Prop => (forall y2 : int, ~ (y1 y2)) /\ ((exists y2 : nat, y1 (int_of_num y2)) \/ (exists y2 : nat, y1 (int_neg (int_of_num y2))))) y0).
Definition term194 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term248 := @eq Prop (forall y0 : int, exists y1 : nat, (y0 = (int_of_num y1)) \/ (y0 = (int_neg (int_of_num y1)))).
Definition term247 := @eq Prop (forall y0 : int, exists y1 : nat, (fun y2 : int => fun y3 : nat => (y2 = (int_of_num y3)) \/ (y2 = (int_neg (int_of_num y3)))) y0 y1).
Definition term205 (x0 : int) (x1 : int -> Prop) (x2 : nat) := ((x1 x0) /\ ((forall y0 : nat, ~ (x1 (int_of_num y0))) /\ (forall y0 : nat, ~ (x1 (int_neg (int_of_num y0)))))) \/ ((fun y0 : nat => (forall y1 : int, ~ (x1 y1)) /\ ((x1 (int_of_num y0)) \/ (x1 (int_neg (int_of_num y0))))) x2).
Definition term199 (x0 : int) (x1 : int -> Prop) := exists y0 : nat, ((x1 x0) /\ ((forall y1 : nat, ~ (x1 (int_of_num y1))) /\ (forall y1 : nat, ~ (x1 (int_neg (int_of_num y1)))))) \/ ((fun y1 : nat => (forall y2 : int, ~ (x1 y2)) /\ ((x1 (int_of_num y1)) \/ (x1 (int_neg (int_of_num y1))))) y0).
Definition term142 (x0 : int -> Prop) (x1 : nat) := (fun y0 : nat => (x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0)))) x1.
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term200 (x0 : int -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : int, ~ (x0 y1)) /\ ((x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0))))) x1.
Definition term42 (x0 : nat -> Prop) := ~ (ex x0).
Definition term33 (x0 : int -> Prop) := ~ (ex x0).
Definition term9 := ~ (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))).
Definition term215 (x0 : int) := exists y0 : nat, ((fun y1 : nat => x0 = (int_of_num y1)) y0) \/ ((fun y1 : nat => x0 = (int_neg (int_of_num y1))) y0).
Definition term120 (x0 : int -> Prop) := exists y0 : nat, ((fun y1 : nat => x0 (int_of_num y1)) y0) \/ ((fun y1 : nat => x0 (int_neg (int_of_num y1))) y0).
Definition term295 (x0 : int -> nat) (x1 : int) := (x1 = (int_neg (int_of_num (x0 x1)))) \/ (x1 = (int_of_num (x0 x1))).
Definition term183 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => (x0 y1) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) y0.
Definition term88 (x0 : type925) (x1 : type925) := (exists y0 : int -> Prop, x0 y0) \/ (exists y0 : int -> Prop, x1 y0).
Definition term189 (x0 : int) (x1 : int -> Prop) := ((fun y0 : int => (x1 y0) /\ ((forall y1 : nat, ~ (x1 (int_of_num y1))) /\ (forall y1 : nat, ~ (x1 (int_neg (int_of_num y1)))))) x0) \/ (exists y0 : nat, (forall y1 : int, ~ (x1 y1)) /\ ((x1 (int_of_num y0)) \/ (x1 (int_neg (int_of_num y0))))).
Definition term296 (x0 : int -> nat) (x1 : int) := int_neg (int_of_num (x0 x1)).
Definition term294 (x0 : int -> nat) (x1 : int) := (x1 = (int_of_num (x0 x1))) -> ~ (x1 = (int_of_num (x0 x1))).
Definition term326 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := (x0 (int_neg (int_of_num (x1 x2)))) -> False.
Definition term308 (x0 : int) (x1 : int -> Prop) (x2 : int) := @eq Prop ((~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2)))).
Definition term8 := (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False.
Definition term30 (x0 : int -> Prop) := exists y0 : int, x0 y0.
Definition term134 (x0 : int -> Prop) := exists y0 : nat, (x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0))).
Definition term43 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term286 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ (x1 x0)) /\ (x1 x2).
Definition term35 (x0 : int -> Prop) := ~ (exists y0 : int, x0 y0).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term71 (x0 : int -> Prop) := (exists y0 : int, x0 y0) /\ ((forall y0 : nat, ~ (x0 (int_of_num y0))) /\ (forall y0 : nat, ~ (x0 (int_neg (int_of_num y0))))).
Definition term257 := fun y0 : int -> nat => forall y1 : int, (y1 = (int_of_num (y0 y1))) \/ (y1 = (int_neg (int_of_num (y0 y1)))).
Definition term256 := fun y0 : int -> nat => forall y1 : int, (fun y2 : int => fun y3 : nat => (y2 = (int_of_num y3)) \/ (y2 = (int_neg (int_of_num y3)))) y1 (y0 y1).
Definition term254 (x0 : int -> nat) := forall y0 : int, (fun y1 : int => fun y2 : nat => (y1 = (int_of_num y2)) \/ (y1 = (int_neg (int_of_num y2)))) y0 (x0 y0).
Definition term269 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2))).
Definition term70 (x0 : int -> Prop) := (exists y0 : int, x0 y0) /\ (~ ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0))))).
Definition term2 := (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> False.
Definition term271 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := (x0 (int_of_num (x1 x2))) -> ~ (x0 (int_of_num (x1 x2))).
Definition term114 := fun y0 : int -> Prop => exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2))))).
Definition term39 (x0 : int -> Prop) (x1 : int) := ~ (x0 x1).
Definition term87 (x0 : type925) (x1 : type925) := exists y0 : int -> Prop, (x0 y0) \/ (x1 y0).
Definition term284 (x0 : int -> Prop) (x1 : int) := ~ (~ (x0 x1)).
Definition term191 (x0 : int -> Prop) := fun y0 : int => ((fun y1 : int => (x0 y1) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) y0) \/ (exists y1 : nat, (forall y2 : int, ~ (x0 y2)) /\ ((x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1))))).
Definition term291 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := ((~ (x0 (int_of_num (x1 x2)))) /\ (x0 x2)) -> ~ (x2 = (int_of_num (x1 x2))).
Definition term67 (x0 : int -> Prop) := (~ (exists y0 : int, x0 y0)) /\ ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0)))).
Definition term68 (x0 : int -> Prop) := (forall y0 : int, ~ (x0 y0)) /\ ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0)))).
Definition term135 (x0 : int -> Prop) := (forall y0 : int, ~ (x0 y0)) /\ (exists y0 : nat, (x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0)))).
Definition term260 (x0 : int -> nat) (x1 : int) := (fun y0 : int => (y0 = (int_of_num (x0 y0))) \/ (y0 = (int_neg (int_of_num (x0 y0))))) x1.
Definition term222 (x0 : int) := exists y0 : nat, (fun y1 : nat => x0 = (int_neg (int_of_num y1))) y0.
Definition term218 (x0 : int) := exists y0 : nat, (fun y1 : nat => x0 = (int_of_num y1)) y0.
Definition term202 (x0 : int -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : int, ~ (x0 y2)) /\ ((x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1))))) y0.
Definition term144 (x0 : int -> Prop) := exists y0 : nat, (fun y1 : nat => (x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1)))) y0.
Definition term32 := fun y0 : int -> Prop => (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))).
Definition term152 := fun y0 : int -> Prop => exists y1 : nat, (forall y2 : int, ~ (y0 y2)) /\ ((y0 (int_of_num y1)) \/ (y0 (int_neg (int_of_num y1)))).
Definition term314 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term27 (x0 : int -> Prop) := or (exists y0 : nat, x0 (int_of_num y0)).
Definition term297 (x0 : int -> nat) (x1 : int) := @eq Prop ((x1 = (int_of_num (x0 x1))) \/ (x1 = (int_neg (int_of_num (x0 x1))))).
Definition term17 (x0 : int) := exists y0 : nat, x0 = (int_of_num y0).
Definition term72 (x0 : int -> Prop) := or ((exists y0 : int, x0 y0) /\ (~ ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0)))))).
Definition term264 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term278 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term204 (x0 : int) (x1 : int -> Prop) := @eq Prop (((x1 x0) /\ ((forall y0 : nat, ~ (x1 (int_of_num y0))) /\ (forall y0 : nat, ~ (x1 (int_neg (int_of_num y0)))))) \/ (exists y0 : nat, (forall y1 : int, ~ (x1 y1)) /\ ((x1 (int_of_num y0)) \/ (x1 (int_neg (int_of_num y0)))))).
Definition term203 (x0 : int) (x1 : int -> Prop) := @eq Prop (((x1 x0) /\ ((forall y0 : nat, ~ (x1 (int_of_num y0))) /\ (forall y0 : nat, ~ (x1 (int_neg (int_of_num y0)))))) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : int, ~ (x1 y2)) /\ ((x1 (int_of_num y1)) \/ (x1 (int_neg (int_of_num y1))))) y0)).
Definition term16 (x0 : int) := fun y0 : nat => x0 = (int_of_num y0).
Definition term130 (x0 : int -> Prop) (x1 : nat) := ((fun y0 : nat => x0 (int_of_num y0)) x1) \/ ((fun y0 : nat => x0 (int_neg (int_of_num y0))) x1).
Definition term98 := @eq Prop (exists y0 : int -> Prop, ((fun y1 : int -> Prop => (exists y2 : int, y1 y2) /\ ((forall y2 : nat, ~ (y1 (int_of_num y2))) /\ (forall y2 : nat, ~ (y1 (int_neg (int_of_num y2)))))) y0) \/ ((fun y1 : int -> Prop => (forall y2 : int, ~ (y1 y2)) /\ ((exists y2 : nat, y1 (int_of_num y2)) \/ (exists y2 : nat, y1 (int_neg (int_of_num y2))))) y0)).
Definition term56 (x0 : int -> Prop) (x1 : nat) := ~ (x0 (int_neg (int_of_num x1))).
Definition term324 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := ~ (x0 (int_neg (int_of_num (x1 x2)))).
Definition term309 (x0 : int -> Prop) (x1 : int) (x2 : int) := @eq Prop ((x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2)))).
Definition term226 (x0 : int) (x1 : nat) := or (x0 = (int_of_num x1)).
Definition term111 (x0 : int -> Prop) (x1 : Prop) := (exists y0 : int, x0 y0) /\ x1.
Definition term96 (x0 : int -> Prop) := ((fun y0 : int -> Prop => (exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1)))))) x0) \/ ((fun y0 : int -> Prop => (forall y1 : int, ~ (y0 y1)) /\ ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1))))) x0).
Definition term292 (x0 : int -> nat) (x1 : int) := int_of_num (x0 x1).
Definition term53 (x0 : int -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 (int_neg (int_of_num y1))) y0).
Definition term45 (x0 : int -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term13 (x0 : nat) := int_neg (int_of_num x0).
Definition term132 (x0 : int -> Prop) := fun y0 : nat => ((fun y1 : nat => x0 (int_of_num y1)) y0) \/ ((fun y1 : nat => x0 (int_neg (int_of_num y1))) y0).
Definition term251 (x0 : int -> nat) (x1 : int) := (x1 = (int_of_num (x0 x1))) \/ (x1 = (int_neg (int_of_num (x0 x1)))).
Definition term64 (x0 : int -> Prop) := ~ ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0)))).
Definition term242 (x0 : int) (x1 : nat) := (fun y0 : int => fun y1 : nat => (y0 = (int_of_num y1)) \/ (y0 = (int_neg (int_of_num y1)))) x0 x1.
Definition term149 (x0 : int -> Prop) := fun y0 : nat => (forall y1 : int, ~ (x0 y1)) /\ ((fun y1 : nat => (x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1)))) y0).
Definition term59 (x0 : int -> Prop) := forall y0 : nat, ~ (x0 (int_neg (int_of_num y0))).
Definition term51 (x0 : int -> Prop) := forall y0 : nat, ~ (x0 (int_of_num y0)).
Definition term323 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := (~ (x0 (int_neg (int_of_num (x1 x2))))) -> x0 (int_neg (int_of_num (x1 x2))).
Definition term160 := or (exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, (y1 y2) /\ ((forall y3 : nat, ~ (y1 (int_of_num y3))) /\ (forall y3 : nat, ~ (y1 (int_neg (int_of_num y3)))))) y0).
Definition term103 := or (exists y0 : int -> Prop, (fun y1 : int -> Prop => (exists y2 : int, y1 y2) /\ ((forall y2 : nat, ~ (y1 (int_of_num y2))) /\ (forall y2 : nat, ~ (y1 (int_neg (int_of_num y2)))))) y0).
Definition term331 (x0 : int -> Prop) (x1 : nat) := (~ (x0 (int_neg (int_of_num x1)))) -> x0 (int_neg (int_of_num x1)).
Definition term182 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => (x0 y1) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) y0.
Definition term240 := fun y0 : int => fun y1 : nat => (y0 = (int_of_num y1)) \/ (y0 = (int_neg (int_of_num y1))).
Definition term310 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ ((~ (x0 = x2)) \/ (~ (x1 x0)))) -> x1 x2.
Definition term261 (x0 : int -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 (int_of_num y0))) x1.
Definition term293 (x0 : int -> nat) (x1 : int) := ~ (x1 = (int_of_num (x0 x1))).
Definition term167 (x0 : int -> Prop) := or (exists y0 : int, (x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1)))))).
Definition term12 := (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> ~ (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))).
Definition term48 (x0 : int -> Prop) (x1 : nat) := ~ (x0 (int_of_num x1)).
Definition term156 := exists y0 : int -> Prop, ((fun y1 : int -> Prop => exists y2 : int, (y1 y2) /\ ((forall y3 : nat, ~ (y1 (int_of_num y3))) /\ (forall y3 : nat, ~ (y1 (int_neg (int_of_num y3)))))) y0) \/ ((fun y1 : int -> Prop => exists y2 : nat, (forall y3 : int, ~ (y1 y3)) /\ ((y1 (int_of_num y2)) \/ (y1 (int_neg (int_of_num y2))))) y0).
Definition term89 := exists y0 : int -> Prop, ((fun y1 : int -> Prop => (exists y2 : int, y1 y2) /\ ((forall y2 : nat, ~ (y1 (int_of_num y2))) /\ (forall y2 : nat, ~ (y1 (int_neg (int_of_num y2)))))) y0) \/ ((fun y1 : int -> Prop => (forall y2 : int, ~ (y1 y2)) /\ ((exists y2 : nat, y1 (int_of_num y2)) \/ (exists y2 : nat, y1 (int_neg (int_of_num y2))))) y0).
Definition term201 (x0 : int -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : int, ~ (x0 y2)) /\ ((x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1))))) y0.
Definition term171 := fun y0 : int -> Prop => (exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2)))))) \/ (exists y1 : nat, (forall y2 : int, ~ (y0 y2)) /\ ((y0 (int_of_num y1)) \/ (y0 (int_neg (int_of_num y1))))).
Definition term268 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term25 (x0 : int -> Prop) := fun y0 : nat => x0 (int_of_num y0).
Definition term198 (x0 : int) (x1 : int -> Prop) := ((x1 x0) /\ ((forall y0 : nat, ~ (x1 (int_of_num y0))) /\ (forall y0 : nat, ~ (x1 (int_neg (int_of_num y0)))))) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : int, ~ (x1 y2)) /\ ((x1 (int_of_num y1)) \/ (x1 (int_neg (int_of_num y1))))) y0).
Definition term55 (x0 : int -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 (int_neg (int_of_num y0))) x1).
Definition term47 (x0 : int -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 (int_of_num y0)) x1).
Definition term151 (x0 : int -> Prop) := exists y0 : nat, (forall y1 : int, ~ (x0 y1)) /\ ((x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0)))).
Definition term329 (x0 : int -> Prop) (x1 : int) := (x0 x1) -> False.
Definition term99 := @eq Prop (exists y0 : int -> Prop, ((exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1)))))) \/ ((forall y1 : int, ~ (y0 y1)) /\ ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))).
Definition term181 (x0 : int) (x1 : int -> Prop) := (x1 x0) /\ ((forall y0 : nat, ~ (x1 (int_of_num y0))) /\ (forall y0 : nat, ~ (x1 (int_neg (int_of_num y0))))).
Definition term24 (x0 : int -> Prop) (x1 : nat) := x0 (int_of_num x1).
Definition term249 (x0 : int -> nat) (x1 : int) := (fun y0 : int => fun y1 : nat => (y0 = (int_of_num y1)) \/ (y0 = (int_neg (int_of_num y1)))) x1 (x0 x1).
Definition term231 (x0 : int) := exists y0 : nat, (x0 = (int_of_num y0)) \/ (x0 = (int_neg (int_of_num y0))).
Definition term104 := or (exists y0 : int -> Prop, (exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1)))))).
Definition term270 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := ~ (x0 (int_of_num (x1 x2))).
Definition term146 (x0 : int -> Prop) := @eq Prop ((forall y0 : int, ~ (x0 y0)) /\ (exists y0 : nat, (x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0))))).
Definition term145 (x0 : int -> Prop) := @eq Prop ((forall y0 : int, ~ (x0 y0)) /\ (exists y0 : nat, (fun y1 : nat => (x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1)))) y0)).
Definition term184 (x0 : int -> Prop) := or (exists y0 : int, (fun y1 : int => (x0 y1) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) y0).
Definition term147 (x0 : int -> Prop) (x1 : nat) := (forall y0 : int, ~ (x0 y0)) /\ ((fun y0 : nat => (x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0)))) x1).
Definition term82 := fun y0 : int -> Prop => ~ ((fun y1 : int -> Prop => (exists y2 : int, y1 y2) = ((exists y2 : nat, y1 (int_of_num y2)) \/ (exists y2 : nat, y1 (int_neg (int_of_num y2))))) y0).
Definition term290 (x0 : int -> nat) (x1 : int -> Prop) (x2 : int) := (~ (x1 (int_of_num (x0 x2)))) /\ (x1 x2).
Definition term238 := forall y0 : int, exists y1 : nat, (fun y2 : int => fun y3 : nat => (y2 = (int_of_num y3)) \/ (y2 = (int_neg (int_of_num y3)))) y0 y1.
Definition term236 (x0 : type1552) := forall y0 : int, exists y1 : nat, x0 y0 y1.
Definition term233 := forall y0 : int, exists y1 : nat, (y0 = (int_of_num y1)) \/ (y0 = (int_neg (int_of_num y1))).
Definition term57 (x0 : int -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 (int_neg (int_of_num y1))) y0).
Definition term49 (x0 : int -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term118 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term188 (x0 : int) (x1 : int -> Prop) := or ((x1 x0) /\ ((forall y0 : nat, ~ (x1 (int_of_num y0))) /\ (forall y0 : nat, ~ (x1 (int_neg (int_of_num y0)))))).
Definition term15 (x0 : int) := exists y0 : nat, x0 = (int_neg (int_of_num y0)).
Definition term78 (x0 : type925) := exists y0 : int -> Prop, ~ (x0 y0).
Definition term253 (x0 : int -> nat) := fun y0 : int => (y0 = (int_of_num (x0 y0))) \/ (y0 = (int_neg (int_of_num (x0 y0)))).
Definition term211 (x0 : int -> Prop) := exists y0 : int, exists y1 : nat, ((x0 y0) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) \/ ((forall y2 : int, ~ (x0 y2)) /\ ((x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1))))).
Definition term282 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ (x1 x0)) /\ (~ (~ (x1 x2))).
Definition term221 (x0 : int) := fun y0 : nat => (fun y1 : nat => x0 = (int_neg (int_of_num y1))) y0.
Definition term95 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, ~ (y0 y1)) /\ ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term93 (x0 : int -> Prop) := (fun y0 : int -> Prop => (exists y1 : int, y0 y1) /\ ((forall y1 : nat, ~ (y0 (int_of_num y1))) /\ (forall y1 : nat, ~ (y0 (int_neg (int_of_num y1)))))) x0.
Definition term259 (x0 : int -> Prop) (x1 : int) := and (x0 x1).
Definition term62 (x0 : int -> Prop) := (~ (exists y0 : nat, x0 (int_of_num y0))) /\ (~ (exists y0 : nat, x0 (int_neg (int_of_num y0)))).
Definition term287 (x0 : int) (x1 : int -> Prop) (x2 : int) := imp (~ ((x1 x0) \/ (~ (x1 x2)))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term277 (x0 : int -> Prop) (x1 : int) (x2 : int) := (~ ((x0 x2) \/ (~ (x0 x1)))) -> ~ (x1 = x2).
Definition term229 (x0 : int) := fun y0 : nat => ((fun y1 : nat => x0 = (int_of_num y1)) y0) \/ ((fun y1 : nat => x0 = (int_neg (int_of_num y1))) y0).
Definition term250 (x0 : int -> nat) (x1 : int) := (fun y0 : nat => (x1 = (int_of_num y0)) \/ (x1 = (int_neg (int_of_num y0)))) (x0 x1).
Definition term219 (x0 : int) := or (exists y0 : nat, (fun y1 : nat => x0 = (int_of_num y1)) y0).
Definition term123 (x0 : int -> Prop) := or (exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term5 := ((~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False) -> (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False.
Definition term304 (x0 : int) (x1 : int -> Prop) (x2 : int) := (~ (x2 = x0)) \/ (~ (x1 x2)).
Definition term313 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term7 := (((~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False) -> (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False) -> ((~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False) -> (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))) -> (forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) -> False.
Definition term227 (x0 : int) (x1 : nat) := ((fun y0 : nat => x0 = (int_of_num y0)) x1) \/ ((fun y0 : nat => x0 = (int_neg (int_of_num y0))) x1).
Definition term75 (x0 : int -> Prop) := ((exists y0 : int, x0 y0) /\ ((forall y0 : nat, ~ (x0 (int_of_num y0))) /\ (forall y0 : nat, ~ (x0 (int_neg (int_of_num y0)))))) \/ ((forall y0 : int, ~ (x0 y0)) /\ ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0))))).
Definition term161 (x0 : int -> Prop) := (fun y0 : int -> Prop => exists y1 : nat, (forall y2 : int, ~ (y0 y2)) /\ ((y0 (int_of_num y1)) \/ (y0 (int_neg (int_of_num y1))))) x0.
Definition term157 (x0 : int -> Prop) := (fun y0 : int -> Prop => exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2)))))) x0.
Definition term235 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term298 (x0 : int -> nat) (x1 : int) := @eq Prop ((x1 = (int_neg (int_of_num (x0 x1)))) \/ (x1 = (int_of_num (x0 x1)))).
Definition term37 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => x0 y0) x1.
Definition term307 (x0 : int -> Prop) (x1 : int) (x2 : int) := (x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2))).
Definition term230 (x0 : int) := fun y0 : nat => (x0 = (int_of_num y0)) \/ (x0 = (int_neg (int_of_num y0))).
Definition term10 := forall y0 : int, (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1))).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term318 (x0 : int) (x1 : int -> Prop) (x2 : int) := imp ((x2 = x0) /\ (x1 x2)).
Definition term196 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term125 (x0 : int -> Prop) := exists y0 : nat, (fun y1 : nat => x0 (int_neg (int_of_num y1))) y0.
Definition term122 (x0 : int -> Prop) := exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0.
Definition term69 (x0 : int -> Prop) := and (exists y0 : int, x0 y0).
Definition term217 (x0 : int) := fun y0 : nat => (fun y1 : nat => x0 = (int_of_num y1)) y0.
Definition term281 (x0 : int) (x1 : int -> Prop) (x2 : int) := ~ ((x1 x0) \/ (~ (x1 x2))).
Definition term192 (x0 : int -> Prop) := fun y0 : int => ((x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1)))))) \/ (exists y1 : nat, (forall y2 : int, ~ (x0 y2)) /\ ((x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1))))).
Definition term28 (x0 : int -> Prop) := (exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term272 (x0 : int -> Prop) (x1 : int -> nat) (x2 : int) := x0 (int_of_num (x1 x2)).
Definition term131 (x0 : int -> Prop) (x1 : nat) := (x0 (int_of_num x1)) \/ (x0 (int_neg (int_of_num x1))).
Definition term190 (x0 : int) (x1 : int -> Prop) := ((x1 x0) /\ ((forall y0 : nat, ~ (x1 (int_of_num y0))) /\ (forall y0 : nat, ~ (x1 (int_neg (int_of_num y0)))))) \/ (exists y0 : nat, (forall y1 : int, ~ (x1 y1)) /\ ((x1 (int_of_num y0)) \/ (x1 (int_neg (int_of_num y0))))).
Definition term320 (x0 : int -> nat) (x1 : int -> Prop) (x2 : int) := (x2 = (int_neg (int_of_num (x0 x2)))) /\ (x1 x2).
Definition term117 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term265 (x0 : int) (x1 : int -> Prop) (x2 : int) := ((x1 x2) = (x1 x0)) -> (x1 x0) \/ (~ (x1 x2)).
Definition term11 := imp (~ (forall y0 : int -> Prop, (exists y1 : int, y0 y1) = ((exists y1 : nat, y0 (int_of_num y1)) \/ (exists y1 : nat, y0 (int_neg (int_of_num y1)))))).
Definition term273 (x0 : Prop) := x0 -> ~ x0.
Definition term246 := fun y0 : int => exists y1 : nat, (fun y2 : int => fun y3 : nat => (y2 = (int_of_num y3)) \/ (y2 = (int_neg (int_of_num y3)))) y0 y1.
Definition term208 (x0 : int) (x1 : int -> Prop) := fun y0 : nat => ((x1 x0) /\ ((forall y1 : nat, ~ (x1 (int_of_num y1))) /\ (forall y1 : nat, ~ (x1 (int_neg (int_of_num y1)))))) \/ ((forall y1 : int, ~ (x1 y1)) /\ ((x1 (int_of_num y0)) \/ (x1 (int_neg (int_of_num y0))))).
Definition term176 (x0 : int -> Prop) (x1 : Prop) := exists y0 : int, (x0 y0) \/ x1.
Definition term301 (x0 : int -> nat) (x1 : int) := ~ (x1 = (int_neg (int_of_num (x0 x1)))).
Definition term141 (x0 : int -> Prop) := exists y0 : nat, (forall y1 : int, ~ (x0 y1)) /\ ((fun y1 : nat => (x0 (int_of_num y1)) \/ (x0 (int_neg (int_of_num y1)))) y0).
Definition term36 (x0 : int -> Prop) := forall y0 : int, ~ ((fun y1 : int => x0 y1) y0).
Definition term224 (x0 : int) := @eq Prop ((exists y0 : nat, x0 = (int_of_num y0)) \/ (exists y0 : nat, x0 = (int_neg (int_of_num y0)))).
Definition term223 (x0 : int) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (int_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => x0 = (int_neg (int_of_num y1))) y0)).
Definition term186 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (x0 y0) /\ ((forall y1 : nat, ~ (x0 (int_of_num y1))) /\ (forall y1 : nat, ~ (x0 (int_neg (int_of_num y1)))))) \/ (exists y0 : nat, (forall y1 : int, ~ (x0 y1)) /\ ((x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0)))))).
Definition term185 (x0 : int -> Prop) := @eq Prop ((exists y0 : int, (fun y1 : int => (x0 y1) /\ ((forall y2 : nat, ~ (x0 (int_of_num y2))) /\ (forall y2 : nat, ~ (x0 (int_neg (int_of_num y2)))))) y0) \/ (exists y0 : nat, (forall y1 : int, ~ (x0 y1)) /\ ((x0 (int_of_num y0)) \/ (x0 (int_neg (int_of_num y0)))))).
Definition term165 := @eq Prop ((exists y0 : int -> Prop, exists y1 : int, (y0 y1) /\ ((forall y2 : nat, ~ (y0 (int_of_num y2))) /\ (forall y2 : nat, ~ (y0 (int_neg (int_of_num y2)))))) \/ (exists y0 : int -> Prop, exists y1 : nat, (forall y2 : int, ~ (y0 y2)) /\ ((y0 (int_of_num y1)) \/ (y0 (int_neg (int_of_num y1)))))).
Definition term164 := @eq Prop ((exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : int, (y1 y2) /\ ((forall y3 : nat, ~ (y1 (int_of_num y3))) /\ (forall y3 : nat, ~ (y1 (int_neg (int_of_num y3)))))) y0) \/ (exists y0 : int -> Prop, (fun y1 : int -> Prop => exists y2 : nat, (forall y3 : int, ~ (y1 y3)) /\ ((y1 (int_of_num y2)) \/ (y1 (int_neg (int_of_num y2))))) y0)).
Definition term127 (x0 : int -> Prop) := @eq Prop ((exists y0 : nat, x0 (int_of_num y0)) \/ (exists y0 : nat, x0 (int_neg (int_of_num y0)))).
Definition term126 (x0 : int -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => x0 (int_neg (int_of_num y1))) y0)).
