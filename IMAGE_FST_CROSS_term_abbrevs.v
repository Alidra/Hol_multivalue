Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term149 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => (x0 y0) /\ ((exists y1 : a1, x1 y1) /\ (x2 = y0)).
Definition term266 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := exists y0 : a1, (fun y1 : a1 => ((x2 x1) /\ ((x0 y1) /\ (x3 = x1))) /\ (~ (x2 x3))) y0.
Definition term230 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := exists y0 : a1, (fun y1 : a1 => (x0 x3) /\ ((x1 y1) /\ (x2 = x3))) y0.
Definition term142 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := exists y0 : a1, (fun y1 : a1 => (x0 y1) /\ (x1 = x2)) y0.
Definition term165 (a0 : Type') (x0 : a0 -> Prop) := and (exists y0 : a0, x0 y0).
Definition term303 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := @eq Prop ((~ (x0 x3)) \/ (forall y0 : a1, (~ (x1 y0)) \/ (~ (x2 = x3)))).
Definition term302 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := @eq Prop ((~ (x0 x3)) \/ (forall y0 : a1, (fun y1 : a1 => (~ (x1 y1)) \/ (~ (x2 = x3))) y0)).
Definition term277 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => exists y1 : a1, (((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) \/ ((forall y2 : a0, (~ (x1 y2)) \/ ((forall y3 : a1, ~ (x0 y3)) \/ (~ (x2 = y2)))) /\ (x1 x2)).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term318 := (~ False) -> False.
Definition term330 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (~ ((~ (forall y2 : a1, ~ (y1 y2))) -> forall y2 : a0, (exists y3 : a0, exists y4 : a1, (y0 y3) /\ ((y1 y4) /\ (y2 = y3))) = (y0 y2))) -> False) x0.
Definition term295 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term134 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (x0 x3) /\ (exists y0 : a1, (fun y1 : a1 => (x1 y1) /\ (x2 = x3)) y0).
Definition term77 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term50 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := @IN a0 x0 (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x2)).
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term256 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := or (exists y0 : a1, ((x2 x1) /\ ((x0 y0) /\ (x3 = x1))) /\ (~ (x2 x3))).
Definition term71 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : prod a0 a1) := (fun y0 : prod a0 a1 => x0 = (@fst a0 a1 y0)) x1.
Definition term247 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (fun y1 : a0 => exists y2 : a1, ((x1 y1) /\ ((x0 y2) /\ (x2 = y1))) /\ (~ (x1 x2))) y0) \/ ((forall y0 : a0, (~ (x1 y0)) \/ ((forall y1 : a1, ~ (x0 y1)) \/ (~ (x2 = y0)))) /\ (x1 x2)).
Definition term223 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => ((fun y1 : a0 => exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (x2 = y1))) y0) /\ (~ (x1 x2)).
Definition term269 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((exists y0 : a1, ((x2 x0) /\ ((x1 y0) /\ (x3 = x0))) /\ (~ (x2 x3))) \/ ((forall y0 : a0, (~ (x2 y0)) \/ ((forall y1 : a1, ~ (x1 y1)) \/ (~ (x3 = y0)))) /\ (x2 x3))).
Definition term268 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((exists y0 : a1, (fun y1 : a1 => ((x2 x0) /\ ((x1 y1) /\ (x3 = x0))) /\ (~ (x2 x3))) y0) \/ ((forall y0 : a0, (~ (x2 y0)) \/ ((forall y1 : a1, ~ (x1 y1)) \/ (~ (x3 = y0)))) /\ (x2 x3))).
Definition term137 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) (x4 : a1) := (x0 x3) /\ ((fun y0 : a1 => (x1 y0) /\ (x2 = x3)) x4).
Definition term209 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := and (exists y0 : a0, exists y1 : a1, (x0 y0) /\ ((x1 y1) /\ (x2 = y0))).
Definition term76 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) := (fun y0 : prod a0 a1 => x0 = (@fst a0 a1 y0)) (@pair a0 a1 x1 x2).
Definition term130 (x0 : Prop) := ~ (~ x0).
Definition term259 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => ((fun y1 : a0 => exists y2 : a1, ((x1 y1) /\ ((x0 y2) /\ (x2 = y1))) /\ (~ (x1 x2))) y0) \/ ((forall y1 : a0, (~ (x1 y1)) \/ ((forall y2 : a1, ~ (x0 y2)) \/ (~ (x2 = y1)))) /\ (x1 x2)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y0 x1)) = (exists y1 : a0, (x0 = (y0 y1)) /\ (@IN a0 y1 x1)).
Definition term274 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := fun y0 : a1 => ((fun y1 : a1 => ((x2 x0) /\ ((x1 y1) /\ (x3 = x0))) /\ (~ (x2 x3))) y0) \/ ((forall y1 : a0, (~ (x2 y1)) \/ ((forall y2 : a1, ~ (x1 y2)) \/ (~ (x3 = y1)))) /\ (x2 x3)).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1207 a0 a1) (x2 : type1210 a0 a1) := @IN a0 x0 (@IMAGE (prod a0 a1) a0 x1 x2).
Definition term219 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := and ((fun y0 : a0 => exists y1 : a1, (x0 y0) /\ ((x1 y1) /\ (x2 = y0))) x3).
Definition term160 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (~ (forall y2 : a1, ~ (y1 y2))) -> forall y2 : a0, (exists y3 : a0, (y0 y3) /\ ((exists y4 : a1, y1 y4) /\ (y2 = y3))) = (y0 y2).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := @eq Prop (exists y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 x0 x1)) /\ (x2 = (@fst a0 a1 y0))).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := @eq Prop (exists y0 : prod a0 a1, (x0 = (@fst a0 a1 y0)) /\ (@IN (prod a0 a1) y0 (@CROSS a1 a0 x1 x2))).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1)) = y0) (@EMPTY a0).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : type1207 a0 a1) (x2 : type1210 a0 a1) := exists y0 : prod a0 a1, (x0 = (x1 y0)) /\ (@IN (prod a0 a1) y0 x2).
Definition term198 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := and (~ (exists y0 : a0, (x0 y0) /\ ((exists y1 : a1, x1 y1) /\ (x2 = y0)))).
Definition term323 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0) (x3 : a0) := ~ ((x0 x1) /\ (x2 = x3)).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := and ((x1 = (@EMPTY a1)) -> (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1)) = y0) (@EMPTY a0)).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term234 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) (x4 : a1) := and ((fun y0 : a1 => (x0 x3) /\ ((x1 y0) /\ (x2 = x3))) x4).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term265 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := fun y0 : a1 => (fun y1 : a1 => ((x2 x1) /\ ((x0 y1) /\ (x3 = x1))) /\ (~ (x2 x3))) y0.
Definition term175 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term296 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term169 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term287 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop ((forall y0 : a1, ~ (x0 y0)) \/ (~ (x1 = x2))).
Definition term286 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop ((forall y0 : a1, (fun y1 : a1 => ~ (x0 y1)) y0) \/ (~ (x1 = x2))).
Definition term186 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := ~ ((exists y0 : a1, x0 y0) /\ (x1 = x2)).
Definition term193 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (x0 y0) /\ ((exists y1 : a1, x1 y1) /\ (x2 = y0))) x3.
Definition term189 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (~ (x0 x3)) \/ ((forall y0 : a1, ~ (x1 y0)) \/ (~ (x2 = x3))).
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 x1).
Definition term131 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term123 (x0 : Prop) := (~ x0) -> False.
Definition term54 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0))) = (@IN a0 y0 x1).
Definition term139 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := @eq Prop (exists y0 : a1, (x0 x3) /\ ((fun y1 : a1 => (x1 y1) /\ (x2 = x3)) y0)).
Definition term245 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term281 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := (forall y0 : a1, (fun y1 : a1 => ~ (x0 y1)) y0) \/ (~ (x1 = x2)).
Definition term314 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = y0) (@COND (a0 -> Prop) (x0 = (@EMPTY a1)) (@EMPTY a0) x1).
Definition term213 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (fun y0 : a0 => exists y1 : a1, (x0 y0) /\ ((x1 y1) /\ (x2 = y0))) x3.
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (~ (x0 = (@EMPTY a1))) -> (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = y0) x1.
Definition term292 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := fun y0 : a1 => (~ (x0 y0)) \/ (~ (x1 = x2)).
Definition term312 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) (x4 : a1) := (fun y0 : a1 => (~ (x0 x3)) \/ ((~ (x1 y0)) \/ (~ (x2 = x3)))) x4.
Definition term252 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (exists y0 : a0, (fun y1 : a0 => exists y2 : a1, ((x1 y1) /\ ((x0 y2) /\ (x2 = y1))) /\ (~ (x1 x2))) y0).
Definition term278 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, exists y1 : a1, (((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) \/ ((forall y2 : a0, (~ (x1 y2)) \/ ((forall y3 : a1, ~ (x0 y3)) \/ (~ (x2 = y2)))) /\ (x1 x2)).
Definition term242 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2)).
Definition term118 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := exists y0 : a0, exists y1 : a1, (x0 y0) /\ ((x1 y1) /\ (x2 = y0)).
Definition term95 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := exists y0 : a0, exists y1 : a1, (@IN a0 y0 x0) /\ ((@IN a1 y1 x1) /\ (x2 = y0)).
Definition term89 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := exists y0 : a0, exists y1 : a1, (@IN a0 y0 x0) /\ ((@IN a1 y1 x1) /\ (x2 = (@fst a0 a1 (@pair a0 a1 y0 y1)))).
Definition term69 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := exists y0 : a0, exists y1 : a1, (@IN a0 y0 x0) /\ ((@IN a1 y1 x1) /\ ((fun y2 : prod a0 a1 => x2 = (@fst a0 a1 y2)) (@pair a0 a1 y0 y1))).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1210 a0 a1) := exists y0 : a0, exists y1 : a1, (@IN a0 y0 x0) /\ ((@IN a1 y1 x1) /\ (x2 (@pair a0 a1 y0 y1))).
Definition term332 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 y0)) = (@COND (a0 -> Prop) (y0 = (@EMPTY a1)) (@EMPTY a0) x0).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = y0) (@COND (a0 -> Prop) (x0 = (@EMPTY a1)) (@EMPTY a0) x1)).
Definition term147 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := (exists y0 : a1, x0 y0) /\ (x1 = x2).
Definition term233 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((exists y0 : a1, (x2 x1) /\ ((x0 y0) /\ (x3 = x1))) /\ (~ (x2 x3))).
Definition term232 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((exists y0 : a1, (fun y1 : a1 => (x2 x1) /\ ((x0 y1) /\ (x3 = x1))) y0) /\ (~ (x2 x3))).
Definition term218 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, exists y1 : a1, (x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))).
Definition term217 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (x2 = y1))) y0) /\ (~ (x1 x2))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (@IN a1 y0 (@IMAGE a0 a1 y2 y1)) = (exists y3 : a0, (y0 = (y2 y3)) /\ (@IN a0 y3 y1))) x0.
Definition term199 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := and (forall y0 : a0, (~ (x0 y0)) \/ ((forall y1 : a1, ~ (x1 y1)) \/ (~ (x2 = y0)))).
Definition term129 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := ~ (~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term231 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := and (exists y0 : a1, (fun y1 : a1 => (x0 x3) /\ ((x1 y1) /\ (x2 = x3))) y0).
Definition term194 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := ~ ((fun y0 : a0 => (x0 y0) /\ ((exists y1 : a1, x1 y1) /\ (x2 = y0))) x3).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, x0 y0.
Definition term141 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := fun y0 : a1 => (fun y1 : a1 => (x0 y1) /\ (x1 = x2)) y0.
Definition term132 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := ((x0 = (@EMPTY a1)) -> (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = (@EMPTY a0)) /\ ((~ (x0 = (@EMPTY a1))) -> (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = x1).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@CROSS a0 a1 y0 (@EMPTY a0)) = (@EMPTY (prod a1 a0))) x0.
Definition term327 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0) := (x0 x1) /\ (x2 = x2).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := imp (~ (x0 = (@EMPTY a0))).
Definition term153 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (exists y1 : a0, (x1 y1) /\ ((exists y2 : a1, x0 y2) /\ (y0 = y1))) = (x1 y0).
Definition term121 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => forall y1 : a1 -> Prop, forall y2 : a0 -> Prop, (exists y3 : prod a1 a0, (@IN (prod a1 a0) y3 (@CROSS a0 a1 y1 y2)) /\ (y0 y3)) = (exists y3 : a1, exists y4 : a0, (@IN a1 y3 y1) /\ ((@IN a0 y4 y2) /\ (y0 (@pair a1 a0 y3 y4))))) x0.
Definition term212 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, ((fun y1 : a0 => exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (x2 = y1))) y0) /\ (~ (x1 x2)).
Definition term321 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term316 (x0 : Prop) := (~ x0) -> x0.
Definition term58 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : prod a0 a1) := (@IN (prod a0 a1) x3 (@CROSS a1 a0 x0 x1)) /\ (x2 = (@fst a0 a1 x3)).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => x0 y1) y0).
Definition term114 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) (x3 : a0) (x4 : a0) := (x0 x4) /\ ((x1 x2) /\ (x3 = x4)).
Definition term98 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (exists y1 : a0, exists y2 : a1, (@IN a0 y1 x1) /\ ((@IN a1 y2 x0) /\ (y0 = y1))) = (@IN a0 y0 x1).
Definition term65 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (exists y1 : prod a0 a1, (@IN (prod a0 a1) y1 (@CROSS a1 a0 x1 x0)) /\ (y0 = (@fst a0 a1 y1))) = (@IN a0 y0 x1).
Definition term56 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (exists y1 : prod a0 a1, (y0 = (@fst a0 a1 y1)) /\ (@IN (prod a0 a1) y1 (@CROSS a1 a0 x1 x0))) = (@IN a0 y0 x1).
Definition term204 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((exists y0 : a0, (x1 y0) /\ ((exists y1 : a1, x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))).
Definition term267 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := or (exists y0 : a1, (fun y1 : a1 => ((x2 x1) /\ ((x0 y1) /\ (x3 = x1))) /\ (~ (x2 x3))) y0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1223 a0 a1) := forall y0 : a0 -> Prop, (exists y1 : prod a1 a0, (@IN (prod a1 a0) y1 (@CROSS a0 a1 x0 y0)) /\ (x1 y1)) = (exists y1 : a1, exists y2 : a0, (@IN a1 y1 x0) /\ ((@IN a0 y2 y0) /\ (x1 (@pair a1 a0 y1 y2)))).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := @IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1).
Definition term7 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y0 /\ y1) = (y1 /\ y0)) x0.
Definition term322 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term93 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := exists y0 : a1, (@IN a0 x3 x0) /\ ((@IN a1 y0 x1) /\ (x2 = x3)).
Definition term57 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : prod a0 a1) (x2 : a0 -> Prop) (x3 : a1 -> Prop) := (x0 = (@fst a0 a1 x1)) /\ (@IN (prod a0 a1) x1 (@CROSS a1 a0 x2 x3)).
Definition term258 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (exists y0 : a1, ((x2 x0) /\ ((x1 y0) /\ (x3 = x0))) /\ (~ (x2 x3))) \/ ((forall y0 : a0, (~ (x2 y0)) \/ ((forall y1 : a1, ~ (x1 y1)) \/ (~ (x3 = y0)))) /\ (x2 x3)).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term299 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) (x3 : a1) := (fun y0 : a1 => (~ (x0 y0)) \/ (~ (x1 = x2))) x3.
Definition term235 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) (x3 : a0) (x4 : a0) := and ((x0 x4) /\ ((x1 x2) /\ (x3 = x4))).
Definition term279 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term40 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := @COND (a0 -> Prop) (x0 = (@EMPTY a1)) (@EMPTY a0) x1.
Definition term108 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y1 y0)) = (exists y2 : a0, (x0 = (y1 y2)) /\ (@IN a0 y2 y0))) x1.
Definition term91 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1) (x2 : a1 -> Prop) (x3 : a0) (x4 : a0) := (@IN a0 x4 x0) /\ ((@IN a1 x1 x2) /\ (x3 = x4)).
Definition term301 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := forall y0 : a1, (fun y1 : a1 => (~ (x0 y1)) \/ (~ (x1 = x2))) y0.
Definition term51 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := exists y0 : prod a0 a1, (x0 = (@fst a0 a1 y0)) /\ (@IN (prod a0 a1) y0 (@CROSS a1 a0 x1 x2)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1223 a0 a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : prod a1 a0, (@IN (prod a1 a0) y1 (@CROSS a0 a1 x0 y0)) /\ (x1 y1)) = (exists y1 : a1, exists y2 : a0, (@IN a1 y1 x0) /\ ((@IN a0 y2 y0) /\ (x1 (@pair a1 a0 y1 y2))))) x2.
Definition term251 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, (fun y1 : a0 => exists y2 : a1, ((x1 y1) /\ ((x0 y2) /\ (x2 = y1))) /\ (~ (x1 x2))) y0.
Definition term215 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := exists y0 : a0, (fun y1 : a0 => exists y2 : a1, (x0 y1) /\ ((x1 y2) /\ (x2 = y1))) y0.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : type686 a0) (x3 : a0 -> Prop) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term87 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => exists y1 : a1, (@IN a0 y0 x0) /\ ((@IN a1 y1 x1) /\ ((fun y2 : prod a0 a1 => x2 = (@fst a0 a1 y2)) (@pair a0 a1 y0 y1))).
Definition term75 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := @eq Prop (exists y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 x0 x1)) /\ ((fun y1 : prod a0 a1 => x2 = (@fst a0 a1 y1)) y0)).
Definition term195 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 y1) /\ ((exists y2 : a1, x1 y2) /\ (x2 = y1))) y0).
Definition term113 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0) (x3 : a0) := (x0 x1) /\ (x2 = x3).
Definition term203 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (x1 y0) /\ ((exists y1 : a1, x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1223 a0 a1) := exists y0 : a1, exists y1 : a0, (@IN a1 y0 x0) /\ ((@IN a0 y1 x1) /\ (x2 (@pair a1 a0 y0 y1))).
Definition term225 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, (exists y1 : a1, (x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 x0 (@IMAGE a0 a1 x1 x2).
Definition term224 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => (exists y1 : a1, (x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2)).
Definition term70 (a0 : Type') (a1 : Type') (x0 : a0) := fun y0 : prod a0 a1 => x0 = (@fst a0 a1 y0).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0))).
Definition term82 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) (x4 : a1) := (@IN a0 x3 x0) /\ ((@IN a1 x4 x1) /\ (x2 = (@fst a0 a1 (@pair a0 a1 x3 x4)))).
Definition term320 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term102 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (~ (x0 = (@EMPTY a1))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (@IN a0 y1 x1) /\ ((@IN a1 y2 x0) /\ (y0 = y1))) = (@IN a0 y0 x1).
Definition term328 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) (x3 : a0) := (x0 x3) /\ ((x1 x2) /\ (x3 = x3)).
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term158 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, (~ (forall y1 : a1, ~ (y0 y1))) -> forall y1 : a0, (exists y2 : a0, (x0 y2) /\ ((exists y3 : a1, y0 y3) /\ (y1 = y2))) = (x0 y1).
Definition term290 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0) (x3 : a0) := (~ (x0 x1)) \/ (~ (x2 = x3)).
Definition term244 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) \/ ((forall y0 : a0, (~ (x1 y0)) \/ ((forall y1 : a1, ~ (x0 y1)) \/ (~ (x2 = y0)))) /\ (x1 x2)).
Definition term249 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := (fun y0 : a0 => exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) x3.
Definition term66 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1210 a0 a1) := exists y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 x0 x1)) /\ (x2 y0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1223 a0 a1) := exists y0 : prod a1 a0, (@IN (prod a1 a0) y0 (@CROSS a0 a1 x0 x1)) /\ (x2 y0).
Definition term150 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := exists y0 : a0, (x0 y0) /\ ((exists y1 : a1, x1 y1) /\ (x2 = y0)).
Definition term90 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (@IN a1 x0 x1) /\ (x2 = x3).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := exists y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 x0 x1)) /\ (x2 = (@fst a0 a1 y0)).
Definition term307 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := fun y0 : a1 => (~ (x0 x3)) \/ ((~ (x1 y0)) \/ (~ (x2 = x3))).
Definition term294 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (~ (x0 x3)) \/ (forall y0 : a1, (~ (x1 y0)) \/ (~ (x2 = x3))).
Definition term9 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (x0 /\ y0) = (y0 /\ x0)) x1.
Definition term109 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term126 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := ((~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False) -> (~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False.
Definition term74 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 x0 x1)) /\ ((fun y1 : prod a0 a1 => x2 = (@fst a0 a1 y1)) y0).
Definition term211 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, (fun y1 : a0 => exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (x2 = y1))) y0) /\ (~ (x1 x2)).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term166 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((exists y0 : a0, (x1 y0) /\ ((exists y1 : a1, x0 y1) /\ (x2 = y0))) = (x1 x2))) -> False.
Definition term308 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := forall y0 : a1, (~ (x0 x3)) \/ ((~ (x1 y0)) \/ (~ (x2 = x3))).
Definition term94 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => exists y1 : a1, (@IN a0 y0 x0) /\ ((@IN a1 y1 x1) /\ (x2 = y0)).
Definition term271 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0) (x3 : a0 -> Prop) (x4 : a0) := or (((x3 x2) /\ ((x0 x1) /\ (x4 = x2))) /\ (~ (x3 x4))).
Definition term138 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := fun y0 : a1 => (x0 x3) /\ ((fun y1 : a1 => (x1 y1) /\ (x2 = x3)) y0).
Definition term190 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := ~ ((x0 x3) /\ ((exists y0 : a1, x1 y0) /\ (x2 = x3))).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term161 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (~ ((~ (forall y2 : a1, ~ (y1 y2))) -> forall y2 : a0, (exists y3 : a0, exists y4 : a1, (y0 y3) /\ ((y1 y4) /\ (y2 = y3))) = (y0 y2))) -> False.
Definition term282 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := forall y0 : a1, ((fun y1 : a1 => ~ (x0 y1)) y0) \/ (~ (x1 = x2)).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term117 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => exists y1 : a1, (x0 y0) /\ ((x1 y1) /\ (x2 = y0)).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term241 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2)).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term331 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => (~ ((~ (forall y1 : a1, ~ (y0 y1))) -> forall y1 : a0, (exists y2 : a0, exists y3 : a1, (x0 y2) /\ ((y0 y3) /\ (y1 = y2))) = (x0 y1))) -> False) x1.
Definition term72 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := and (@IN (prod a0 a1) x0 (@CROSS a1 a0 x1 x2)).
Definition term311 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (fun y0 : a0 => forall y1 : a1, (~ (x0 y0)) \/ ((~ (x1 y1)) \/ (~ (x2 = y0)))) x3.
Definition term313 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term305 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) (x3 : a0) (x4 : a0) := (~ (x0 x4)) \/ ((~ (x1 x2)) \/ (~ (x3 = x4))).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0)).
Definition term304 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) (x4 : a1) := (~ (x0 x3)) \/ ((fun y0 : a1 => (~ (x1 y0)) \/ (~ (x2 = x3))) x4).
Definition term208 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := @eq Prop ((x0 x3) /\ (exists y0 : a1, (x1 y0) /\ (x2 = x3))).
Definition term207 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := @eq Prop ((x0 x3) /\ (exists y0 : a1, (fun y1 : a1 => (x1 y1) /\ (x2 = x3)) y0)).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := ~ (x0 = (@EMPTY a0)).
Definition term79 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) (x3 : a1) := (@IN a1 x3 x0) /\ ((fun y0 : prod a0 a1 => x1 = (@fst a0 a1 y0)) (@pair a0 a1 x2 x3)).
Definition term261 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, (exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) \/ ((forall y1 : a0, (~ (x1 y1)) \/ ((forall y2 : a1, ~ (x0 y2)) \/ (~ (x2 = y1)))) /\ (x1 x2)).
Definition term148 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (x0 x3) /\ ((exists y0 : a1, x1 y0) /\ (x2 = x3)).
Definition term293 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := forall y0 : a1, (~ (x0 y0)) \/ (~ (x1 = x2)).
Definition term300 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := fun y0 : a1 => (fun y1 : a1 => (~ (x0 y1)) \/ (~ (x1 = x2))) y0.
Definition term239 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := fun y0 : a1 => ((x2 x1) /\ ((x0 y0) /\ (x3 = x1))) /\ (~ (x2 x3)).
Definition term210 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (exists y0 : a0, exists y1 : a1, (x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2)).
Definition term237 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0) (x3 : a0 -> Prop) (x4 : a0) := ((x3 x2) /\ ((x0 x1) /\ (x4 = x2))) /\ (~ (x3 x4)).
Definition term52 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := @eq Prop (@IN a0 x0 (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x2))).
Definition term283 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term288 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, ~ (x0 y0)).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term27 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := ((x0 = (@EMPTY a1)) -> (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = y0) (@EMPTY a0)) /\ ((~ (x0 = (@EMPTY a1))) -> (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = y0) x1).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term80 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) (x3 : a1) := (@IN a1 x3 x0) /\ (x1 = (@fst a0 a1 (@pair a0 a1 x2 x3))).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a1 -> Prop) (x4 : a0 -> Prop) := (x1 -> (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x2 x3)) = y0) x0) /\ ((~ x1) -> (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x2 x3)) = y0) x4).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term156 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a1 -> Prop => (~ (forall y1 : a1, ~ (y0 y1))) -> forall y1 : a0, (exists y2 : a0, (x0 y2) /\ ((exists y3 : a1, y0 y3) /\ (y1 = y2))) = (x0 y1).
Definition term44 (a0 : Type') (a1 : Type') := forall y0 : a1 -> Prop, (@CROSS a0 a1 y0 (@EMPTY a0)) = (@EMPTY (prod a1 a0)).
Definition term236 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a1) (x3 : a0 -> Prop) (x4 : a0) := ((fun y0 : a1 => (x3 x1) /\ ((x0 y0) /\ (x4 = x1))) x2) /\ (~ (x3 x4)).
Definition term21 (a0 : Type') (x0 : type686 a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := x0 (@COND (a0 -> Prop) x1 x2 x3).
Definition term143 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := exists y0 : a1, (x0 y0) /\ (x1 = x2).
Definition term155 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a1 -> Prop => (~ ((~ (forall y1 : a1, ~ (y0 y1))) -> forall y1 : a0, (exists y2 : a0, exists y3 : a1, (x0 y2) /\ ((y0 y3) /\ (y1 = y2))) = (x0 y1))) -> False.
Definition term200 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (exists y0 : a0, (x1 y0) /\ ((exists y1 : a1, x0 y1) /\ (x2 = y0)))) /\ (x1 x2).
Definition term229 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := fun y0 : a1 => (fun y1 : a1 => (x0 x3) /\ ((x1 y1) /\ (x2 = x3))) y0.
Definition term275 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := fun y0 : a1 => (((x2 x0) /\ ((x1 y0) /\ (x3 = x0))) /\ (~ (x2 x3))) \/ ((forall y1 : a0, (~ (x2 y1)) \/ ((forall y2 : a1, ~ (x1 y2)) \/ (~ (x3 = y1)))) /\ (x2 x3)).
Definition term280 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term144 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (x0 x3) /\ (exists y0 : a1, (x1 y0) /\ (x2 = x3)).
Definition term116 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := exists y0 : a1, (x0 x3) /\ ((x1 y0) /\ (x2 = x3)).
Definition term127 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (((~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False) -> (~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False) -> (~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False.
Definition term157 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, (~ ((~ (forall y1 : a1, ~ (y0 y1))) -> forall y1 : a0, (exists y2 : a0, exists y3 : a1, (x0 y2) /\ ((y0 y3) /\ (y1 = y2))) = (x0 y1))) -> False.
Definition term183 (a0 : Type') (x0 : a0 -> Prop) := or (forall y0 : a0, ~ (x0 y0)).
Definition term297 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (~ (x0 x3)) \/ (forall y0 : a1, (fun y1 : a1 => (~ (x1 y1)) \/ (~ (x2 = x3))) y0).
Definition term133 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := exists y0 : a1, (x0 x3) /\ ((fun y1 : a1 => (x1 y1) /\ (x2 = x3)) y0).
Definition term329 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) (x3 : a0) := ((x0 x3) /\ ((x1 x2) /\ (x3 = x3))) -> False.
Definition term326 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) (x3 : a0) (x4 : a0) := ((x0 x4) /\ ((x1 x2) /\ (x3 = x4))) -> False.
Definition term181 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term240 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := exists y0 : a1, ((x2 x1) /\ ((x0 y0) /\ (x3 = x1))) /\ (~ (x2 x3)).
Definition term333 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 y0 y1)) = (@COND (a0 -> Prop) (y1 = (@EMPTY a1)) (@EMPTY a0) y0).
Definition term162 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (~ (forall y2 : a1, ~ (y1 y2))) -> forall y2 : a0, (exists y3 : a0, (y0 y3) /\ ((exists y4 : a1, y1 y4) /\ (y2 = y3))) = (y0 y2).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y1 y0)) = (exists y2 : a0, (x0 = (y1 y2)) /\ (@IN a0 y2 y0)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1 -> Prop, forall y1 : a0 -> Prop, (exists y2 : prod a1 a0, (@IN (prod a1 a0) y2 (@CROSS a0 a1 y0 y1)) /\ (x0 y2)) = (exists y2 : a1, exists y3 : a0, (@IN a1 y2 y0) /\ ((@IN a0 y3 y1) /\ (x0 (@pair a1 a0 y2 y3)))).
Definition term238 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := fun y0 : a1 => ((fun y1 : a1 => (x2 x1) /\ ((x0 y1) /\ (x3 = x1))) y0) /\ (~ (x2 x3)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1)) = y0.
Definition term325 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) (x3 : a0) (x4 : a0) := ~ ((x0 x4) /\ ((x1 x2) /\ (x3 = x4))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : Prop) (x3 : a0 -> Prop) (x4 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1)) = y0) (@COND (a0 -> Prop) x2 x3 x4).
Definition term86 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := exists y0 : a1, (@IN a0 x3 x0) /\ ((@IN a1 y0 x1) /\ (x2 = (@fst a0 a1 (@pair a0 a1 x3 y0)))).
Definition term152 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : a0, (x1 y1) /\ ((exists y2 : a1, x0 y2) /\ (y0 = y1))) = (x1 y0).
Definition term120 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0).
Definition term273 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a1 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := (((x3 x1) /\ ((x2 x0) /\ (x4 = x1))) /\ (~ (x3 x4))) \/ ((forall y0 : a0, (~ (x3 y0)) \/ ((forall y1 : a1, ~ (x2 y1)) \/ (~ (x4 = y0)))) /\ (x3 x4)).
Definition term243 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (exists y0 : a0, exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))).
Definition term103 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a1, (@IN a1 y0 x0) = (@IN a1 y0 (@EMPTY a1)))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (@IN a0 y1 x1) /\ ((@IN a1 y2 x0) /\ (y0 = y1))) = (@IN a0 y0 x1).
Definition term167 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((exists y0 : a0, (x1 y0) /\ ((exists y1 : a1, x0 y1) /\ (x2 = y0))) = (x1 x2)).
Definition term159 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (~ ((~ (forall y2 : a1, ~ (y1 y2))) -> forall y2 : a0, (exists y3 : a0, exists y4 : a1, (y0 y3) /\ ((y1 y4) /\ (y2 = y3))) = (y0 y2))) -> False.
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (x1 = (@EMPTY a1)) -> (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1)) = (@EMPTY a0).
Definition term196 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => (~ (x0 y0)) \/ ((forall y1 : a1, ~ (x1 y1)) \/ (~ (x2 = y0))).
Definition term289 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0) (x3 : a0) := ((fun y0 : a1 => ~ (x0 y0)) x1) \/ (~ (x2 = x3)).
Definition term84 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := fun y0 : a1 => (@IN a0 x3 x0) /\ ((@IN a1 y0 x1) /\ (x2 = (@fst a0 a1 (@pair a0 a1 x3 y0)))).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (fun y0 : a0 -> a1 => (@IN a1 x0 (@IMAGE a0 a1 y0 x1)) = (exists y1 : a0, (x0 = (y0 y1)) /\ (@IN a0 y1 x1))) x2.
Definition term32 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (~ (x0 = (@EMPTY a1))) -> (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = x1.
Definition term306 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := fun y0 : a1 => (~ (x0 x3)) \/ ((fun y1 : a1 => (~ (x1 y1)) \/ (~ (x2 = x3))) y0).
Definition term184 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := (~ (exists y0 : a1, x0 y0)) \/ (~ (x1 = x2)).
Definition term88 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => exists y1 : a1, (@IN a0 y0 x0) /\ ((@IN a1 y1 x1) /\ (x2 = (@fst a0 a1 (@pair a0 a1 y0 y1)))).
Definition term191 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := ~ (exists y0 : a0, (x0 y0) /\ ((exists y1 : a1, x1 y1) /\ (x2 = y0))).
Definition term255 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := or ((fun y0 : a0 => exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) x3).
Definition term85 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := exists y0 : a1, (@IN a0 x3 x0) /\ ((@IN a1 y0 x1) /\ ((fun y1 : prod a0 a1 => x2 = (@fst a0 a1 y1)) (@pair a0 a1 x3 y0))).
Definition term310 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := forall y0 : a0, forall y1 : a1, (~ (x0 y0)) \/ ((~ (x1 y1)) \/ (~ (x2 = y0))).
Definition term92 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := fun y0 : a1 => (@IN a0 x3 x0) /\ ((@IN a1 y0 x1) /\ (x2 = x3)).
Definition term248 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, ((fun y1 : a0 => exists y2 : a1, ((x1 y1) /\ ((x0 y2) /\ (x2 = y1))) /\ (~ (x1 x2))) y0) \/ ((forall y1 : a0, (~ (x1 y1)) \/ ((forall y2 : a1, ~ (x0 y2)) \/ (~ (x2 = y1)))) /\ (x1 x2)).
Definition term226 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (exists y0 : a1, (fun y1 : a1 => (x2 x1) /\ ((x0 y1) /\ (x3 = x1))) y0) /\ (~ (x2 x3)).
Definition term319 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term221 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 => exists y1 : a1, (x2 y0) /\ ((x0 y1) /\ (x3 = y0))) x1) /\ (~ (x2 x3)).
Definition term276 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := exists y0 : a1, (((x2 x0) /\ ((x1 y0) /\ (x3 = x0))) /\ (~ (x2 x3))) \/ ((forall y1 : a0, (~ (x2 y1)) \/ ((forall y2 : a1, ~ (x1 y2)) \/ (~ (x3 = y1)))) /\ (x2 x3)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := and ((x1 = (@EMPTY a1)) -> (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1)) = (@EMPTY a0)).
Definition term97 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : a0, exists y2 : a1, (@IN a0 y1 x1) /\ ((@IN a1 y2 x0) /\ (y0 = y1))) = (@IN a0 y0 x1).
Definition term64 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : prod a0 a1, (@IN (prod a0 a1) y1 (@CROSS a1 a0 x1 x0)) /\ (y0 = (@fst a0 a1 y1))) = (@IN a0 y0 x1).
Definition term55 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (exists y1 : prod a0 a1, (y0 = (@fst a0 a1 y1)) /\ (@IN (prod a0 a1) y1 (@CROSS a1 a0 x1 x0))) = (@IN a0 y0 x1).
Definition term262 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (exists y0 : a1, (fun y1 : a1 => ((x2 x0) /\ ((x1 y1) /\ (x3 = x0))) /\ (~ (x2 x3))) y0) \/ ((forall y0 : a0, (~ (x2 y0)) \/ ((forall y1 : a1, ~ (x1 y1)) \/ (~ (x3 = y0)))) /\ (x2 x3)).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0)).
Definition term202 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := and (exists y0 : a0, (x0 y0) /\ ((exists y1 : a1, x1 y1) /\ (x2 = y0))).
Definition term228 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) (x4 : a1) := (fun y0 : a1 => (x0 x3) /\ ((x1 y0) /\ (x2 = x3))) x4.
Definition term136 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) (x3 : a1) := (fun y0 : a1 => (x0 y0) /\ (x1 = x2)) x3.
Definition term317 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term324 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) (x3 : a0) (x4 : a0) := (~ (x0 x4)) \/ (~ ((x1 x2) /\ (x3 = x4))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : a0 -> Prop, (exists y2 : prod a1 a0, (@IN (prod a1 a0) y2 (@CROSS a0 a1 y0 y1)) /\ (x0 y2)) = (exists y2 : a1, exists y3 : a0, (@IN a1 y2 y0) /\ ((@IN a0 y3 y1) /\ (x0 (@pair a1 a0 y2 y3))))) x1.
Definition term264 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) (x4 : a1) := (fun y0 : a1 => ((x2 x1) /\ ((x0 y0) /\ (x3 = x1))) /\ (~ (x2 x3))) x4.
Definition term60 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := fun y0 : prod a0 a1 => (x0 = (@fst a0 a1 y0)) /\ (@IN (prod a0 a1) y0 (@CROSS a1 a0 x1 x2)).
Definition term119 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := @eq Prop (exists y0 : a0, exists y1 : a1, (x0 y0) /\ ((x1 y1) /\ (x2 = y0))).
Definition term96 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := @eq Prop (exists y0 : a0, exists y1 : a1, (@IN a0 y0 x0) /\ ((@IN a1 y1 x1) /\ (x2 = y0))).
Definition term115 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := fun y0 : a1 => (x0 x3) /\ ((x1 y0) /\ (x2 = x3)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := imp (x0 = (@EMPTY a0)).
Definition term188 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := (~ (x0 x3)) \/ (~ ((exists y0 : a1, x1 y0) /\ (x2 = x3))).
Definition term257 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((fun y0 : a0 => exists y1 : a1, ((x2 y0) /\ ((x1 y1) /\ (x3 = y0))) /\ (~ (x2 x3))) x0) \/ ((forall y0 : a0, (~ (x2 y0)) \/ ((forall y1 : a1, ~ (x1 y1)) \/ (~ (x3 = y0)))) /\ (x2 x3)).
Definition term260 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => (exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) \/ ((forall y1 : a0, (~ (x1 y1)) \/ ((forall y2 : a1, ~ (x0 y2)) \/ (~ (x2 = y1)))) /\ (x1 x2)).
Definition term298 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := forall y0 : a1, (~ (x0 x3)) \/ ((fun y1 : a1 => (~ (x1 y1)) \/ (~ (x2 = x3))) y0).
Definition term272 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := ((fun y0 : a1 => ((x3 x0) /\ ((x2 y0) /\ (x4 = x0))) /\ (~ (x3 x4))) x1) \/ ((forall y0 : a0, (~ (x3 y0)) \/ ((forall y1 : a1, ~ (x2 y1)) \/ (~ (x4 = y0)))) /\ (x3 x4)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term309 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => forall y1 : a1, (~ (x0 y0)) \/ ((~ (x1 y1)) \/ (~ (x2 = y0))).
Definition term128 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (((~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False) -> (~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False) -> ((~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False) -> (~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False.
Definition term68 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := exists y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 x0 x1)) /\ ((fun y1 : prod a0 a1 => x2 = (@fst a0 a1 y1)) y0).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0))) = (@IN a0 y0 x1).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = (@COND (a0 -> Prop) (x0 = (@EMPTY a1)) (@EMPTY a0) x1)).
Definition term182 (a0 : Type') (x0 : a0 -> Prop) := or (~ (exists y0 : a0, x0 y0)).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term124 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0))) -> False.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term254 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, exists y1 : a1, ((x1 y0) /\ ((x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) \/ ((forall y0 : a0, (~ (x1 y0)) \/ ((forall y1 : a1, ~ (x0 y1)) \/ (~ (x2 = y0)))) /\ (x1 x2))).
Definition term253 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => exists y2 : a1, ((x1 y1) /\ ((x0 y2) /\ (x2 = y1))) /\ (~ (x1 x2))) y0) \/ ((forall y0 : a0, (~ (x1 y0)) \/ ((forall y1 : a1, ~ (x0 y1)) \/ (~ (x2 = y0)))) /\ (x1 x2))).
Definition term125 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0)).
Definition term59 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := @IN (prod a0 a1) x0 (@CROSS a1 a0 x1 x2).
Definition term201 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, (~ (x1 y0)) \/ ((forall y1 : a1, ~ (x0 y1)) \/ (~ (x2 = y0)))) /\ (x1 x2).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term8 (x0 : Prop) := forall y0 : Prop, (x0 /\ y0) = (y0 /\ x0).
Definition term270 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) (x4 : a1) := or ((fun y0 : a1 => ((x2 x1) /\ ((x0 y0) /\ (x3 = x1))) /\ (~ (x2 x3))) x4).
Definition term216 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := and (exists y0 : a0, (fun y1 : a0 => exists y2 : a1, (x0 y1) /\ ((x1 y2) /\ (x2 = y1))) y0).
Definition term140 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := @eq Prop (exists y0 : a1, (x0 x3) /\ ((x1 y0) /\ (x2 = x3))).
Definition term192 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := forall y0 : a0, ~ ((fun y1 : a0 => (x0 y1) /\ ((exists y2 : a1, x1 y2) /\ (x2 = y1))) y0).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => x0 y1) y0).
Definition term73 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : prod a0 a1) := (@IN (prod a0 a1) x3 (@CROSS a1 a0 x0 x1)) /\ ((fun y0 : prod a0 a1 => x2 = (@fst a0 a1 y0)) x3).
Definition term81 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) (x4 : a1) := (@IN a0 x3 x0) /\ ((@IN a1 x4 x1) /\ ((fun y0 : prod a0 a1 => x2 = (@fst a0 a1 y0)) (@pair a0 a1 x3 x4))).
Definition term83 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := fun y0 : a1 => (@IN a0 x3 x0) /\ ((@IN a1 y0 x1) /\ ((fun y1 : prod a0 a1 => x2 = (@fst a0 a1 y1)) (@pair a0 a1 x3 y0))).
Definition term61 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 x0 x1)) /\ (x2 = (@fst a0 a1 y0)).
Definition term315 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term185 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := (forall y0 : a1, ~ (x0 y0)) \/ (~ (x1 = x2)).
Definition term206 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((exists y0 : a0, (x1 y0) /\ ((exists y1 : a1, x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) \/ ((forall y0 : a0, (~ (x1 y0)) \/ ((forall y1 : a1, ~ (x0 y1)) \/ (~ (x2 = y0)))) /\ (x1 x2)).
Definition term263 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := exists y0 : a1, ((fun y1 : a1 => ((x2 x0) /\ ((x1 y1) /\ (x3 = x0))) /\ (~ (x2 x3))) y0) \/ ((forall y1 : a0, (~ (x2 y1)) \/ ((forall y2 : a1, ~ (x1 y2)) \/ (~ (x3 = y1)))) /\ (x2 x3)).
Definition term284 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term205 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((exists y0 : a0, (x1 y0) /\ ((exists y1 : a1, x0 y1) /\ (x2 = y0))) /\ (~ (x1 x2))) \/ ((~ (exists y0 : a0, (x1 y0) /\ ((exists y1 : a1, x0 y1) /\ (x2 = y0)))) /\ (x1 x2)).
Definition term197 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := forall y0 : a0, (~ (x0 y0)) \/ ((forall y1 : a1, ~ (x1 y1)) \/ (~ (x2 = y0))).
Definition term154 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, (x1 y1) /\ ((exists y2 : a1, x0 y2) /\ (y0 = y1))) = (x1 y0).
Definition term122 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a1, ~ (x0 y0))) -> forall y0 : a0, (exists y1 : a0, exists y2 : a1, (x1 y1) /\ ((x0 y2) /\ (y0 = y1))) = (x1 y0).
Definition term227 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := exists y0 : a1, ((fun y1 : a1 => (x2 x1) /\ ((x0 y1) /\ (x3 = x1))) y0) /\ (~ (x2 x3)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := @eq (a0 -> Prop) (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1)).
Definition term250 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => (fun y1 : a0 => exists y2 : a1, ((x1 y1) /\ ((x0 y2) /\ (x2 = y1))) /\ (~ (x1 x2))) y0.
Definition term214 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := fun y0 : a0 => (fun y1 : a0 => exists y2 : a1, (x0 y1) /\ ((x1 y2) /\ (x2 = y1))) y0.
Definition term111 (a0 : Type') (x0 : a0 -> Prop) := imp (~ (forall y0 : a0, ~ (x0 y0))).
Definition term101 (a0 : Type') (x0 : a0 -> Prop) := imp (~ (forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0)))).
Definition term220 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) (x3 : a0) := and (exists y0 : a1, (x0 x3) /\ ((x1 y0) /\ (x2 = x3))).
Definition term291 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := fun y0 : a1 => ((fun y1 : a1 => ~ (x0 y1)) y0) \/ (~ (x1 = x2)).
Definition term285 (a0 : Type') (x0 : a0 -> Prop) := or (forall y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => x0 y0) x1).
Definition term151 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0) := @eq Prop (exists y0 : a0, (x0 y0) /\ ((exists y1 : a1, x1 y1) /\ (x2 = y0))).
Definition term222 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0) := (exists y0 : a1, (x2 x1) /\ ((x0 y0) /\ (x3 = x1))) /\ (~ (x2 x3)).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (x1 = (@EMPTY a1)) -> (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x0 x1)) = y0) (@EMPTY a0).
Definition term135 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0) := fun y0 : a1 => (x0 y0) /\ (x1 = x2).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IMAGE (prod a0 a1) a0 (@fst a0 a1) (@CROSS a1 a0 x1 x0)) = y0) x1.
