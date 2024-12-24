Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term208 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := x0 (x1 x2).
Definition term151 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => ((fun y1 : ind => ((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) y0) \/ ((fun y1 : ind => (~ ((x0 x1) = (x0 y1))) /\ (x1 = y1)) y0).
Definition term236 (x0 : ind) (x1 : ind -> ind) := (exists y0 : ind, (fun y1 : ind => (((x1 x0) = (x1 y1)) /\ (~ (x0 = y1))) \/ ((~ ((x1 x0) = (x1 y1))) /\ (x0 = y1))) y0) \/ (exists y0 : ind -> ind, forall y1 : ind, (x1 (y0 y1)) = y1).
Definition term221 (x0 : ind -> ind) := (exists y0 : ind, (fun y1 : ind => exists y2 : ind, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) \/ ((~ ((x0 y1) = (x0 y2))) /\ (y1 = y2))) y0) \/ (exists y0 : ind -> ind, forall y1 : ind, (x0 (y0 y1)) = y1).
Definition term12 (x0 : ind -> ind) := imp ((@ONE_ONE ind ind x0) /\ (~ (@ONTO ind ind x0))).
Definition term319 (x0 : ind) (x1 : ind) := and (x0 = x1).
Definition term240 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, (fun y1 : ind => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) \/ ((~ ((x0 x1) = (x0 y1))) /\ (x1 = y1))) y0.
Definition term160 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, (fun y1 : ind => (~ ((x0 x1) = (x0 y1))) /\ (x1 = y1)) y0.
Definition term155 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, (fun y1 : ind => ((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) y0.
Definition term80 (x0 : ind -> Prop) := ~ (all x0).
Definition term295 := (~ False) -> False.
Definition term149 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (~ ((x0 x1) = (x0 x2))) /\ (x1 = x2).
Definition term239 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => (fun y1 : ind => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) \/ ((~ ((x0 x1) = (x0 y1))) /\ (x1 = y1))) y0.
Definition term130 (x0 : ind -> ind) := fun y0 : ind => exists y1 : ind, (x0 y1) = y0.
Definition term267 (x0 : ind) (x1 : ind -> ind) := fun y0 : ind => exists y1 : ind -> ind, ((((x1 x0) = (x1 y0)) /\ (~ (x0 = y0))) \/ ((~ ((x1 x0) = (x1 y0))) /\ (x0 = y0))) \/ (forall y2 : ind, (x1 (y1 y2)) = y2).
Definition term57 (x0 : ind) (x1 : ind -> ind) := exists y0 : ind, x0 = (x1 y0).
Definition term97 (x0 : ind -> ind) (x1 : ind) := (forall y0 : ind, forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ ((fun y0 : ind => forall y1 : ind, ~ (y0 = (x0 y1))) x1).
Definition term36 (x0 : ind -> ind) (x1 : ind) := (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) /\ ((fun y0 : ind => forall y1 : ind, ~ ((x0 y1) = y0)) x1).
Definition term262 (x0 : ind) (x1 : ind) (x2 : ind -> ind) (x3 : ind -> ind) := ((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ ((fun y0 : ind -> ind => forall y1 : ind, (x2 (y0 y1)) = y1) x3).
Definition term331 := exists y0 : ind -> ind, exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1)).
Definition term280 (x0 : ind -> ind) (x1 : ind) := ~ ((x0 x1) = (x0 x1)).
Definition term285 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := (x0 = x2) \/ (~ ((x1 x0) = (x1 x2))).
Definition term24 (x0 : Prop) := ~ (~ x0).
Definition term232 (x0 : ind) (x1 : ind -> ind) := (exists y0 : ind, (((x1 x0) = (x1 y0)) /\ (~ (x0 = y0))) \/ ((~ ((x1 x0) = (x1 y0))) /\ (x0 = y0))) \/ (exists y0 : ind -> ind, forall y1 : ind, (x1 (y0 y1)) = y1).
Definition term203 (x0 : ind -> ind) := fun y0 : ind => exists y1 : ind, (fun y2 : ind => fun y3 : ind => (x0 y3) = y2) y0 y1.
Definition term92 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => forall y1 : ind, ~ (y0 = (x0 y1))) x1.
Definition term33 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => forall y1 : ind, ~ ((x0 y1) = y0)) x1.
Definition term48 := fun y0 : ind -> ind => ((forall y1 : ind, forall y2 : ind, ((y0 y1) = (y0 y2)) -> y1 = y2) /\ (~ (forall y1 : ind, exists y2 : ind, y1 = (y0 y2)))) -> (forall y1 : ind, forall y2 : ind, ((y0 y1) = (y0 y2)) = (y1 = y2)) /\ (exists y1 : ind, forall y2 : ind, ~ ((y0 y2) = y1)).
Definition term245 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := or ((((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))) \/ ((~ ((x0 x1) = (x0 x2))) /\ (x1 = x2))).
Definition term166 (x0 : ind -> ind) := (exists y0 : ind, (fun y1 : ind => exists y2 : ind, ((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) y0) \/ (exists y0 : ind, (fun y1 : ind => exists y2 : ind, (~ ((x0 y1) = (x0 y2))) /\ (y1 = y2)) y0).
Definition term141 (x0 : ind -> ind) (x1 : ind) := (exists y0 : ind, (fun y1 : ind => ((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) y0) \/ (exists y0 : ind, (fun y1 : ind => (~ ((x0 x1) = (x0 y1))) /\ (x1 = y1)) y0).
Definition term255 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := ((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ (exists y0 : ind -> ind, (fun y1 : ind -> ind => forall y2 : ind, (x2 (y1 y2)) = y2) y0).
Definition term101 (x0 : ind -> ind) := exists y0 : ind, (forall y1 : ind, forall y2 : ind, (~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (forall y1 : ind, ~ (y0 = (x0 y1))).
Definition term14 (x0 : ind -> ind) := exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)).
Definition term165 (x0 : ind -> ind) := exists y0 : ind, ((fun y1 : ind => exists y2 : ind, ((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : ind => exists y2 : ind, (~ ((x0 y1) = (x0 y2))) /\ (y1 = y2)) y0).
Definition term140 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, ((fun y1 : ind => ((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) y0) \/ ((fun y1 : ind => (~ ((x0 x1) = (x0 y1))) /\ (x1 = y1)) y0).
Definition term289 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (~ (~ ((x0 x1) = (x0 x2)))) -> x1 = x2.
Definition term316 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term110 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) \/ ((~ ((x0 x1) = (x0 y0))) /\ (x1 = y0)).
Definition term134 (x0 : ind -> ind) := (~ (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1))) \/ (~ (exists y0 : ind, forall y1 : ind, ~ ((x0 y1) = y0))).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term150 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := ((fun y0 : ind => ((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) x2) \/ ((fun y0 : ind => (~ ((x0 x1) = (x0 y0))) /\ (x1 = y0)) x2).
Definition term185 (x0 : ind -> ind) := or ((exists y0 : ind, exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ (exists y0 : ind, exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))).
Definition term209 (x0 : ind -> ind) (x1 : ind -> ind) := fun y0 : ind => (fun y1 : ind => fun y2 : ind => (x0 y2) = y1) y0 (x1 y0).
Definition term98 (x0 : ind) (x1 : ind -> ind) := (forall y0 : ind, forall y1 : ind, (~ ((x1 y0) = (x1 y1))) \/ (y0 = y1)) /\ (forall y0 : ind, ~ (x0 = (x1 y0))).
Definition term37 (x0 : ind -> ind) (x1 : ind) := (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) /\ (forall y0 : ind, ~ ((x0 y0) = x1)).
Definition term28 (x0 : Prop) (x1 : ind -> Prop) := x0 /\ (exists y0 : ind, x1 y0).
Definition term301 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := (~ ((x0 (x1 x2)) = (x0 (x1 x2)))) -> (x0 (x1 x2)) = (x0 (x1 x2)).
Definition term59 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := ((x0 x1) = (x0 x2)) -> x1 = x2.
Definition term274 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := (fun y0 : ind => (x0 (x1 y0)) = y0) x2.
Definition term25 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term17 (x0 : Prop) := (~ x0) -> False.
Definition term217 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term321 (x0 : ind) (x1 : ind) (x2 : ind) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term68 (x0 : ind -> ind) := fun y0 : ind => forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1).
Definition term62 (x0 : ind -> ind) := fun y0 : ind => forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term55 (x0 : ind -> ind) := fun y0 : ind => forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1).
Definition term47 := fun y0 : ind -> ind => (~ (((forall y1 : ind, forall y2 : ind, ((y0 y1) = (y0 y2)) -> y1 = y2) /\ (~ (forall y1 : ind, exists y2 : ind, y1 = (y0 y2)))) -> exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1)))) -> False.
Definition term64 (x0 : ind -> ind) := ~ ((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) /\ (exists y0 : ind, forall y1 : ind, ~ ((x0 y1) = y0))).
Definition term332 := fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1)).
Definition term50 := forall y0 : ind -> ind, ((forall y1 : ind, forall y2 : ind, ((y0 y1) = (y0 y2)) -> y1 = y2) /\ (~ (forall y1 : ind, exists y2 : ind, y1 = (y0 y2)))) -> (forall y1 : ind, forall y2 : ind, ((y0 y1) = (y0 y2)) = (y1 = y2)) /\ (exists y1 : ind, forall y2 : ind, ~ ((y0 y2) = y1)).
Definition term6 (x0 : ind -> ind) := and (@ONE_ONE ind ind x0).
Definition term103 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))) \/ ((~ ((x0 x1) = (x0 x2))) /\ (x1 = x2)).
Definition term288 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term282 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := @eq Prop (~ ((x1 x0) = (x1 x2))).
Definition term142 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => ((x0 x1) = (x0 y0)) /\ (~ (x1 = y0)).
Definition term119 (x0 : ind -> ind) (x1 : ind) := ~ (forall y0 : ind, ~ ((x0 y0) = x1)).
Definition term299 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := (~ ((x0 (x1 x2)) = x2)) -> (x0 (x1 x2)) = x2.
Definition term206 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := (fun y0 : ind => fun y1 : ind => (x0 y1) = y0) x2 (x1 x2).
Definition term46 (x0 : ind -> ind) := ((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) /\ (exists y0 : ind, forall y1 : ind, ~ ((x0 y1) = y0)).
Definition term219 (x0 : ind -> Prop) (x1 : Prop) := (exists y0 : ind, x0 y0) \/ x1.
Definition term26 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term291 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := imp (~ (~ ((x1 x0) = (x1 x2)))).
Definition term125 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, (x0 y0) = x1.
Definition term284 (x0 : Prop) := (~ x0) -> x0.
Definition term108 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => ~ ((fun y1 : ind => ((x0 x1) = (x0 y1)) = (x1 = y1)) y0).
Definition term77 (x0 : ind) (x1 : ind -> ind) := fun y0 : ind => ~ ((fun y1 : ind => x0 = (x1 y1)) y0).
Definition term254 (x0 : Prop) (x1 : type922) := exists y0 : ind -> ind, x0 \/ (x1 y0).
Definition term198 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => fun y1 : ind => (x0 y1) = y0) x1.
Definition term273 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := (fun y0 : ind => ~ (x0 = (x1 y0))) x2.
Definition term163 (x0 : ind -> ind) := fun y0 : ind => (exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ (exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1)).
Definition term312 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term167 (x0 : ind -> ind) := fun y0 : ind => exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)).
Definition term314 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term191 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term309 (x0 : ind) (x1 : ind) (x2 : ind) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (@ONE_ONE a0 a1 y0) = (forall y1 : a0, forall y2 : a0, ((y0 y1) = (y0 y2)) -> y1 = y2)) x0.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (@ONTO a0 a1 y0) = (forall y1 : a1, exists y2 : a0, y1 = (y0 y2))) x0.
Definition term175 (x0 : ind -> ind) := @eq Prop (exists y0 : ind, (exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ (exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))).
Definition term174 (x0 : ind -> ind) := @eq Prop (exists y0 : ind, ((fun y1 : ind => exists y2 : ind, ((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : ind => exists y2 : ind, (~ ((x0 y1) = (x0 y2))) /\ (y1 = y2)) y0)).
Definition term153 (x0 : ind -> ind) (x1 : ind) := @eq Prop (exists y0 : ind, (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) \/ ((~ ((x0 x1) = (x0 y0))) /\ (x1 = y0))).
Definition term152 (x0 : ind -> ind) (x1 : ind) := @eq Prop (exists y0 : ind, ((fun y1 : ind => ((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) y0) \/ ((fun y1 : ind => (~ ((x0 x1) = (x0 y1))) /\ (x1 = y1)) y0)).
Definition term41 (x0 : ind -> ind) := @eq Prop (exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0))).
Definition term40 (x0 : ind -> ind) := @eq Prop (exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ ((fun y1 : ind => forall y2 : ind, ~ ((x0 y2) = y1)) y0)).
Definition term247 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := ((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ (exists y0 : ind -> ind, forall y1 : ind, (x2 (y0 y1)) = y1).
Definition term56 (x0 : ind) (x1 : ind -> ind) := fun y0 : ind => x0 = (x1 y0).
Definition term132 (x0 : ind -> ind) := or (~ (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1))).
Definition term310 (x0 : ind) (x1 : ind) (x2 : ind) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term196 (x0 : ind -> ind) := exists y0 : ind -> ind, forall y1 : ind, (fun y2 : ind => fun y3 : ind => (x0 y3) = y2) y1 (y0 y1).
Definition term194 (x0 : type1547) := exists y0 : ind -> ind, forall y1 : ind, x0 y1 (y0 y1).
Definition term264 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := fun y0 : ind -> ind => ((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ ((fun y1 : ind -> ind => forall y2 : ind, (x2 (y1 y2)) = y2) y0).
Definition term9 (x0 : ind -> ind) := ~ (@ONTO ind ind x0).
Definition term275 (x0 : ind) (x1 : ind) := ~ (x0 = x1).
Definition term148 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => (~ ((x0 x1) = (x0 y0))) /\ (x1 = y0)) x2.
Definition term307 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term27 (x0 : Prop) (x1 : ind -> Prop) := exists y0 : ind, x0 /\ (x1 y0).
Definition term237 (x0 : ind) (x1 : ind -> ind) := exists y0 : ind, ((fun y1 : ind => (((x1 x0) = (x1 y1)) /\ (~ (x0 = y1))) \/ ((~ ((x1 x0) = (x1 y1))) /\ (x0 = y1))) y0) \/ (exists y1 : ind -> ind, forall y2 : ind, (x1 (y1 y2)) = y2).
Definition term222 (x0 : ind -> ind) := exists y0 : ind, ((fun y1 : ind => exists y2 : ind, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) \/ ((~ ((x0 y1) = (x0 y2))) /\ (y1 = y2))) y0) \/ (exists y1 : ind -> ind, forall y2 : ind, (x0 (y1 y2)) = y2).
Definition term323 (x0 : ind) (x1 : ind) (x2 : ind) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term76 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := ~ (x0 = (x1 x2)).
Definition term292 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := imp ((x1 x0) = (x1 x2)).
Definition term329 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := (x2 = (x0 (x1 x2))) -> False.
Definition term330 (x0 : ind -> ind) := (fun y0 : ind -> ind => (~ (((forall y1 : ind, forall y2 : ind, ((y0 y1) = (y0 y2)) -> y1 = y2) /\ (~ (forall y1 : ind, exists y2 : ind, y1 = (y0 y2)))) -> exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1)))) -> False) x0.
Definition term15 (x0 : ind -> ind) := ((@ONE_ONE ind ind x0) /\ (~ (@ONTO ind ind x0))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)).
Definition term173 (x0 : ind -> ind) := fun y0 : ind => ((fun y1 : ind => exists y2 : ind, ((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : ind => exists y2 : ind, (~ ((x0 y1) = (x0 y2))) /\ (y1 = y2)) y0).
Definition term269 (x0 : ind -> ind) := fun y0 : ind => exists y1 : ind, exists y2 : ind -> ind, ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) \/ (forall y3 : ind, (x0 (y2 y3)) = y3).
Definition term283 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := (~ ((x1 x0) = (x1 x2))) -> (x1 x0) = (x1 x2).
Definition term253 (x0 : Prop) (x1 : type922) := x0 \/ (exists y0 : ind -> ind, x1 y0).
Definition term122 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := ~ ((fun y0 : ind => ~ ((x0 y0) = x1)) x2).
Definition term74 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := (fun y0 : ind => x0 = (x1 y0)) x2.
Definition term271 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) x1.
Definition term113 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) x1.
Definition term298 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term186 (x0 : ind -> ind) := ((exists y0 : ind, exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ (exists y0 : ind, exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) \/ (forall y0 : ind, exists y1 : ind, (x0 y1) = y0).
Definition term144 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => ((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) x2.
Definition term279 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => ~ ((x0 y0) = (x0 x1))) x1.
Definition term263 (x0 : ind) (x1 : ind) (x2 : ind -> ind) (x3 : ind -> ind) := ((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ (forall y0 : ind, (x2 (x3 y0)) = y0).
Definition term326 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := (~ (x2 = (x0 (x1 x2)))) -> x2 = (x0 (x1 x2)).
Definition term259 (x0 : ind -> ind) := exists y0 : ind -> ind, (fun y1 : ind -> ind => forall y2 : ind, (x0 (y1 y2)) = y2) y0.
Definition term297 (x0 : ind -> ind) (x1 : ind) := ((x0 x1) = (x0 x1)) -> False.
Definition term287 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := @eq Prop ((x0 = x2) \/ (~ ((x1 x0) = (x1 x2)))).
Definition term121 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => ~ ((x0 y0) = x1)) x2.
Definition term266 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := exists y0 : ind -> ind, ((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ (forall y1 : ind, (x2 (y0 y1)) = y1).
Definition term147 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := or (((x0 x1) = (x0 x2)) /\ (~ (x1 = x2))).
Definition term91 (x0 : ind -> ind) := exists y0 : ind, (forall y1 : ind, forall y2 : ind, (~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ ((fun y1 : ind => forall y2 : ind, ~ (y1 = (x0 y2))) y0).
Definition term29 (x0 : ind -> ind) := exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ ((fun y1 : ind => forall y2 : ind, ~ ((x0 y2) = y1)) y0).
Definition term244 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := or ((fun y0 : ind => (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) \/ ((~ ((x0 x1) = (x0 y0))) /\ (x1 = y0))) x2).
Definition term146 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := or ((fun y0 : ind => ((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) x2).
Definition term54 (x0 : ind -> ind) (x1 : ind) := forall y0 : ind, ((x0 x1) = (x0 y0)) = (x1 = y0).
Definition term168 (x0 : ind -> ind) := fun y0 : ind => exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1).
Definition term51 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := ~ ((x0 x1) = x2).
Definition term20 (x0 : ind -> ind) := ((~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False) -> (~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False.
Definition term195 (x0 : ind -> ind) := forall y0 : ind, exists y1 : ind, (fun y2 : ind => fun y3 : ind => (x0 y3) = y2) y0 y1.
Definition term193 (x0 : type1547) := forall y0 : ind, exists y1 : ind, x0 y0 y1.
Definition term131 (x0 : ind -> ind) := forall y0 : ind, exists y1 : ind, (x0 y1) = y0.
Definition term8 (x0 : ind -> ind) := forall y0 : ind, exists y1 : ind, y0 = (x0 y1).
Definition term302 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := ~ ((x0 (x1 x2)) = (x0 (x1 x2))).
Definition term234 (x0 : ind -> ind) := fun y0 : ind => (exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) \/ (exists y1 : ind -> ind, forall y2 : ind, (x0 (y1 y2)) = y2).
Definition term252 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term313 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term212 (x0 : ind -> ind) (x1 : ind -> ind) := forall y0 : ind, (x0 (x1 y0)) = y0.
Definition term251 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term109 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) \/ ((~ ((x0 x1) = (x0 y0))) /\ (x1 = y0)).
Definition term248 (x0 : ind) (x1 : ind -> ind) := fun y0 : ind => ((fun y1 : ind => (((x1 x0) = (x1 y1)) /\ (~ (x0 = y1))) \/ ((~ ((x1 x0) = (x1 y1))) /\ (x0 = y1))) y0) \/ (exists y1 : ind -> ind, forall y2 : ind, (x1 (y1 y2)) = y2).
Definition term233 (x0 : ind -> ind) := fun y0 : ind => ((fun y1 : ind => exists y2 : ind, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) \/ ((~ ((x0 y1) = (x0 y2))) /\ (y1 = y2))) y0) \/ (exists y1 : ind -> ind, forall y2 : ind, (x0 (y1 y2)) = y2).
Definition term70 (x0 : ind -> Prop) := ~ (ex x0).
Definition term202 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, (fun y1 : ind => fun y2 : ind => (x0 y2) = y1) x1 y0.
Definition term156 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, ((x0 x1) = (x0 y0)) /\ (~ (x1 = y0)).
Definition term128 (x0 : ind -> ind) (x1 : ind) := ~ ((fun y0 : ind => forall y1 : ind, ~ ((x0 y1) = y0)) x1).
Definition term114 (x0 : ind -> ind) (x1 : ind) := ~ ((fun y0 : ind => forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) x1).
Definition term84 (x0 : ind -> ind) (x1 : ind) := ~ ((fun y0 : ind => exists y1 : ind, y0 = (x0 y1)) x1).
Definition term197 (x0 : ind -> ind) := fun y0 : ind => fun y1 : ind => (x0 y1) = y0.
Definition term308 (x0 : ind) (x1 : ind) (x2 : ind) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term49 := forall y0 : ind -> ind, (~ (((forall y1 : ind, forall y2 : ind, ((y0 y1) = (y0 y2)) -> y1 = y2) /\ (~ (forall y1 : ind, exists y2 : ind, y1 = (y0 y2)))) -> exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1)))) -> False.
Definition term129 (x0 : ind -> ind) := fun y0 : ind => ~ ((fun y1 : ind => forall y2 : ind, ~ ((x0 y2) = y1)) y0).
Definition term115 (x0 : ind -> ind) := fun y0 : ind => ~ ((fun y1 : ind => forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) y0).
Definition term85 (x0 : ind -> ind) := fun y0 : ind => ~ ((fun y1 : ind => exists y2 : ind, y1 = (x0 y2)) y0).
Definition term139 (x0 : ind -> Prop) (x1 : ind -> Prop) := (exists y0 : ind, x0 y0) \/ (exists y0 : ind, x1 y0).
Definition term214 (x0 : ind -> ind) := fun y0 : ind -> ind => forall y1 : ind, (x0 (y0 y1)) = y1.
Definition term106 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => ((x0 x1) = (x0 y0)) = (x1 = y0)) x2.
Definition term241 (x0 : ind -> ind) (x1 : ind) := or (exists y0 : ind, (fun y1 : ind => (((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) \/ ((~ ((x0 x1) = (x0 y1))) /\ (x1 = y1))) y0).
Definition term226 (x0 : ind -> ind) := or (exists y0 : ind, (fun y1 : ind => exists y2 : ind, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) \/ ((~ ((x0 y1) = (x0 y2))) /\ (y1 = y2))) y0).
Definition term179 (x0 : ind -> ind) := or (exists y0 : ind, (fun y1 : ind => exists y2 : ind, ((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) y0).
Definition term157 (x0 : ind -> ind) (x1 : ind) := or (exists y0 : ind, (fun y1 : ind => ((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) y0).
Definition term218 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term272 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => (~ ((x0 x1) = (x0 y0))) \/ (x1 = y0)) x2.
Definition term143 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => (~ ((x0 x1) = (x0 y0))) /\ (x1 = y0).
Definition term127 (x0 : ind -> ind) := forall y0 : ind, ~ ((fun y1 : ind => forall y2 : ind, ~ ((x0 y2) = y1)) y0).
Definition term73 (x0 : ind) (x1 : ind -> ind) := forall y0 : ind, ~ ((fun y1 : ind => x0 = (x1 y1)) y0).
Definition term162 (x0 : ind -> ind) (x1 : ind) := (exists y0 : ind, ((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) \/ (exists y0 : ind, (~ ((x0 x1) = (x0 y0))) /\ (x1 = y0)).
Definition term118 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := ~ (~ ((x0 x1) = x2)).
Definition term207 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := (fun y0 : ind => (x0 y0) = x2) (x1 x2).
Definition term4 (x0 : ind -> ind) := (@ONE_ONE ind ind x0) /\ (~ (@ONTO ind ind x0)).
Definition term78 (x0 : ind) (x1 : ind -> ind) := fun y0 : ind => ~ (x0 = (x1 y0)).
Definition term172 (x0 : ind -> ind) (x1 : ind) := ((fun y0 : ind => exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) x1) \/ ((fun y0 : ind => exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1)) x1).
Definition term87 (x0 : ind -> ind) := exists y0 : ind, forall y1 : ind, ~ (y0 = (x0 y1)).
Definition term44 (x0 : ind -> ind) := exists y0 : ind, forall y1 : ind, ~ ((x0 y1) = y0).
Definition term216 (x0 : ind -> ind) := (exists y0 : ind, exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) \/ (exists y0 : ind -> ind, forall y1 : ind, (x0 (y0 y1)) = y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a1, exists y1 : a0, y0 = (x0 y1).
Definition term320 (x0 : ind) (x1 : ind) (x2 : ind) := (x1 = x0) /\ (x1 = x2).
Definition term306 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term296 (x0 : ind -> ind) (x1 : ind) := (~ ((x0 x1) = (x0 x1))) -> (x0 x1) = (x0 x1).
Definition term32 (x0 : ind -> ind) := fun y0 : ind => forall y1 : ind, ~ ((x0 y1) = y0).
Definition term220 (x0 : ind -> Prop) (x1 : Prop) := exists y0 : ind, (x0 y0) \/ x1.
Definition term102 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := ~ (((x0 x1) = (x0 x2)) = (x1 = x2)).
Definition term21 (x0 : ind -> ind) := (((~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False) -> (~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False) -> (~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False.
Definition term124 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => (x0 y0) = x1.
Definition term231 (x0 : ind) (x1 : ind -> ind) := ((fun y0 : ind => exists y1 : ind, (((x1 y0) = (x1 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x1 y0) = (x1 y1))) /\ (y0 = y1))) x0) \/ (exists y0 : ind -> ind, forall y1 : ind, (x1 (y0 y1)) = y1).
Definition term318 (x0 : ind) (x1 : ind) := and (~ (~ (x0 = x1))).
Definition term304 (x0 : ind) (x1 : ind) (x2 : ind) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term135 (x0 : ind -> ind) := (exists y0 : ind, exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) \/ (forall y0 : ind, exists y1 : ind, (x0 y1) = y0).
Definition term60 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => ((x0 x1) = (x0 y0)) -> x1 = y0.
Definition term180 (x0 : ind -> ind) := or (exists y0 : ind, exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))).
Definition term133 (x0 : ind -> ind) := or (exists y0 : ind, exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))).
Definition term161 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, (~ ((x0 x1) = (x0 y0))) /\ (x1 = y0).
Definition term93 (x0 : ind -> ind) := fun y0 : ind => (fun y1 : ind => forall y2 : ind, ~ (y1 = (x0 y2))) y0.
Definition term42 (x0 : ind -> ind) := fun y0 : ind => (fun y1 : ind => forall y2 : ind, ~ ((x0 y2) = y1)) y0.
Definition term256 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := exists y0 : ind -> ind, ((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ ((fun y1 : ind -> ind => forall y2 : ind, (x2 (y1 y2)) = y2) y0).
Definition term261 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := @eq Prop (((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ (exists y0 : ind -> ind, forall y1 : ind, (x2 (y0 y1)) = y1)).
Definition term260 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := @eq Prop (((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ (exists y0 : ind -> ind, (fun y1 : ind -> ind => forall y2 : ind, (x2 (y1 y2)) = y2) y0)).
Definition term104 (x0 : ind -> ind) (x1 : ind) := ~ (forall y0 : ind, ((x0 x1) = (x0 y0)) = (x1 = y0)).
Definition term65 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (~ ((x0 x1) = (x0 x2))) \/ (x1 = x2).
Definition term224 (x0 : ind -> ind) := fun y0 : ind => (fun y1 : ind => exists y2 : ind, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) \/ ((~ ((x0 y1) = (x0 y2))) /\ (y1 = y2))) y0.
Definition term181 (x0 : ind -> ind) := fun y0 : ind => (fun y1 : ind => exists y2 : ind, (~ ((x0 y1) = (x0 y2))) /\ (y1 = y2)) y0.
Definition term176 (x0 : ind -> ind) := fun y0 : ind => (fun y1 : ind => exists y2 : ind, ((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) y0.
Definition term258 (x0 : ind -> ind) := fun y0 : ind -> ind => (fun y1 : ind -> ind => forall y2 : ind, (x0 (y1 y2)) = y2) y0.
Definition term123 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => ~ ((fun y1 : ind => ~ ((x0 y1) = x1)) y0).
Definition term201 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => (fun y1 : ind => fun y2 : ind => (x0 y2) = y1) x1 y0.
Definition term81 (x0 : ind -> Prop) := exists y0 : ind, ~ (x0 y0).
Definition term325 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := (((x0 (x1 x2)) = x2) /\ ((x0 (x1 x2)) = (x0 (x1 x2)))) -> x2 = (x0 (x1 x2)).
Definition term290 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := ~ (~ ((x1 x0) = (x1 x2))).
Definition term58 (x0 : ind -> ind) := fun y0 : ind => exists y1 : ind, y0 = (x0 y1).
Definition term286 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := @eq Prop ((~ ((x0 x1) = (x0 x2))) \/ (x1 = x2)).
Definition term278 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => ~ ((x0 y0) = (x0 x1))) x2.
Definition term126 (x0 : ind -> ind) := ~ (exists y0 : ind, forall y1 : ind, ~ ((x0 y1) = y0)).
Definition term184 (x0 : ind -> ind) := (exists y0 : ind, exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ (exists y0 : ind, exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1)).
Definition term235 (x0 : ind -> ind) := exists y0 : ind, (exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) \/ (exists y1 : ind -> ind, forall y2 : ind, (x0 (y1 y2)) = y2).
Definition term164 (x0 : ind -> ind) := exists y0 : ind, (exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ (exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1)).
Definition term99 (x0 : ind -> ind) := fun y0 : ind => (forall y1 : ind, forall y2 : ind, (~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ ((fun y1 : ind => forall y2 : ind, ~ (y1 = (x0 y2))) y0).
Definition term38 (x0 : ind -> ind) := fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ ((fun y1 : ind => forall y2 : ind, ~ ((x0 y2) = y1)) y0).
Definition term13 (x0 : ind -> ind) := imp ((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, forall y1 : a0, ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term199 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => fun y1 : ind => (x0 y1) = y0) x1 x2.
Definition term23 (x0 : ind -> ind) := ~ (~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))).
Definition term61 (x0 : ind -> ind) (x1 : ind) := forall y0 : ind, ((x0 x1) = (x0 y0)) -> x1 = y0.
Definition term154 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => (fun y1 : ind => ((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) y0.
Definition term200 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => (x0 y0) = x1) x2.
Definition term69 (x0 : ind -> ind) := forall y0 : ind, forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1).
Definition term31 (x0 : ind -> ind) := forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1).
Definition term5 (x0 : ind -> ind) := forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1.
Definition term100 (x0 : ind -> ind) := fun y0 : ind => (forall y1 : ind, forall y2 : ind, (~ ((x0 y1) = (x0 y2))) \/ (y1 = y2)) /\ (forall y1 : ind, ~ (y0 = (x0 y1))).
Definition term39 (x0 : ind -> ind) := fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)).
Definition term315 (x0 : ind) (x1 : ind) (x2 : ind) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term120 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, ~ ((fun y1 : ind => ~ ((x0 y1) = x1)) y0).
Definition term112 (x0 : ind -> ind) := exists y0 : ind, ~ ((fun y1 : ind => forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) y0).
Definition term105 (x0 : ind -> ind) (x1 : ind) := exists y0 : ind, ~ ((fun y1 : ind => ((x0 x1) = (x0 y1)) = (x1 = y1)) y0).
Definition term82 (x0 : ind -> ind) := exists y0 : ind, ~ ((fun y1 : ind => exists y2 : ind, y1 = (x0 y2)) y0).
Definition term111 (x0 : ind -> ind) := ~ (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)).
Definition term10 (x0 : ind -> ind) := ~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)).
Definition term229 (x0 : ind -> ind) (x1 : ind) := or ((fun y0 : ind => exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) x1).
Definition term170 (x0 : ind -> ind) (x1 : ind) := or ((fun y0 : ind => exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) x1).
Definition term238 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := (fun y0 : ind => (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) \/ ((~ ((x0 x1) = (x0 y0))) /\ (x1 = y0))) x2.
Definition term89 (x0 : ind -> ind) := (forall y0 : ind, forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (exists y0 : ind, forall y1 : ind, ~ (y0 = (x0 y1))).
Definition term45 (x0 : ind -> ind) := (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) /\ (exists y0 : ind, forall y1 : ind, ~ ((x0 y1) = y0)).
Definition term294 (x0 : ind) (x1 : ind) := (x0 = x1) -> False.
Definition term333 := fun y0 : ind -> ind => (@ONE_ONE ind ind y0) /\ (~ (@ONTO ind ind y0)).
Definition term246 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := ((fun y0 : ind => (((x2 x0) = (x2 y0)) /\ (~ (x0 = y0))) \/ ((~ ((x2 x0) = (x2 y0))) /\ (x0 = y0))) x1) \/ (exists y0 : ind -> ind, forall y1 : ind, (x2 (y0 y1)) = y1).
Definition term66 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => (~ ((x0 x1) = (x0 y0))) \/ (x1 = y0).
Definition term53 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => ((x0 x1) = (x0 y0)) = (x1 = y0).
Definition term211 (x0 : ind -> ind) (x1 : ind -> ind) := forall y0 : ind, (fun y1 : ind => fun y2 : ind => (x0 y2) = y1) y0 (x1 y0).
Definition term281 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := @eq Prop ((fun y0 : ind => ~ ((x0 y0) = (x0 x1))) x2).
Definition term250 (x0 : ind) (x1 : ind -> ind) := exists y0 : ind, ((((x1 x0) = (x1 y0)) /\ (~ (x0 = y0))) \/ ((~ ((x1 x0) = (x1 y0))) /\ (x0 = y0))) \/ (exists y1 : ind -> ind, forall y2 : ind, (x1 (y1 y2)) = y2).
Definition term324 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := ((x0 (x1 x2)) = x2) /\ ((x0 (x1 x2)) = (x0 (x1 x2))).
Definition term276 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := ~ ((x1 x0) = (x1 x2)).
Definition term249 (x0 : ind) (x1 : ind -> ind) := fun y0 : ind => ((((x1 x0) = (x1 y0)) /\ (~ (x0 = y0))) \/ ((~ ((x1 x0) = (x1 y0))) /\ (x0 = y0))) \/ (exists y1 : ind -> ind, forall y2 : ind, (x1 (y1 y2)) = y2).
Definition term19 (x0 : ind -> ind) := ~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0))).
Definition term293 (x0 : ind) (x1 : ind) := (~ (x0 = x1)) -> x0 = x1.
Definition term96 (x0 : ind -> ind) := @eq Prop ((forall y0 : ind, forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (exists y0 : ind, forall y1 : ind, ~ (y0 = (x0 y1)))).
Definition term95 (x0 : ind -> ind) := @eq Prop ((forall y0 : ind, forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (exists y0 : ind, (fun y1 : ind => forall y2 : ind, ~ (y1 = (x0 y2))) y0)).
Definition term303 (x0 : ind) (x1 : ind) (x2 : ind) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term322 (x0 : ind) (x1 : ind) (x2 : ind) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term223 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) x1.
Definition term171 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1)) x1.
Definition term169 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) x1.
Definition term83 (x0 : ind -> ind) (x1 : ind) := (fun y0 : ind => exists y1 : ind, y0 = (x0 y1)) x1.
Definition term205 (x0 : ind -> ind) := @eq Prop (forall y0 : ind, exists y1 : ind, (x0 y1) = y0).
Definition term204 (x0 : ind -> ind) := @eq Prop (forall y0 : ind, exists y1 : ind, (fun y2 : ind => fun y3 : ind => (x0 y3) = y2) y0 y1).
Definition term145 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := ((x0 x1) = (x0 x2)) /\ (~ (x1 = x2)).
Definition term138 (x0 : ind -> Prop) (x1 : ind -> Prop) := exists y0 : ind, (x0 y0) \/ (x1 y0).
Definition term327 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := ~ (x2 = (x0 (x1 x2))).
Definition term277 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => ~ ((x0 y0) = (x0 x1)).
Definition term22 (x0 : ind -> ind) := (((~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False) -> (~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False) -> ((~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False) -> (~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False.
Definition term34 (x0 : ind -> ind) (x1 : ind) := forall y0 : ind, ~ ((x0 y0) = x1).
Definition term88 (x0 : ind -> ind) := and (forall y0 : ind, forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)).
Definition term35 (x0 : ind -> ind) := and (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)).
Definition term7 (x0 : ind -> ind) := and (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1).
Definition term86 (x0 : ind -> ind) := fun y0 : ind => forall y1 : ind, ~ (y0 = (x0 y1)).
Definition term107 (x0 : ind -> ind) (x1 : ind) (x2 : ind) := ~ ((fun y0 : ind => ((x0 x1) = (x0 y0)) = (x1 = y0)) x2).
Definition term75 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := ~ ((fun y0 : ind => x0 = (x1 y0)) x2).
Definition term63 (x0 : ind -> ind) := (~ ((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) /\ (exists y0 : ind, forall y1 : ind, ~ ((x0 y1) = y0)))) -> False.
Definition term18 (x0 : ind -> ind) := (~ (((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)))) -> False.
Definition term270 (x0 : ind -> ind) := exists y0 : ind, exists y1 : ind, exists y2 : ind -> ind, ((((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) \/ (forall y3 : ind, (x0 (y2 y3)) = y3).
Definition term268 (x0 : ind) (x1 : ind -> ind) := exists y0 : ind, exists y1 : ind -> ind, ((((x1 x0) = (x1 y0)) /\ (~ (x0 = y0))) \/ ((~ ((x1 x0) = (x1 y0))) /\ (x0 = y0))) \/ (forall y2 : ind, (x1 (y1 y2)) = y2).
Definition term183 (x0 : ind -> ind) := exists y0 : ind, exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1).
Definition term178 (x0 : ind -> ind) := exists y0 : ind, exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1)).
Definition term117 (x0 : ind -> ind) := exists y0 : ind, exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1)).
Definition term257 (x0 : ind -> ind) (x1 : ind -> ind) := (fun y0 : ind -> ind => forall y1 : ind, (x0 (y0 y1)) = y1) x1.
Definition term317 (x0 : ind) (x1 : ind) := ~ (~ (x0 = x1)).
Definition term72 (x0 : ind) (x1 : ind -> ind) := ~ (exists y0 : ind, x0 = (x1 y0)).
Definition term265 (x0 : ind) (x1 : ind) (x2 : ind -> ind) := fun y0 : ind -> ind => ((((x2 x0) = (x2 x1)) /\ (~ (x0 = x1))) \/ ((~ ((x2 x0) = (x2 x1))) /\ (x0 = x1))) \/ (forall y1 : ind, (x2 (y0 y1)) = y1).
Definition term305 (x0 : ind) (x1 : ind) := or (~ (x0 = x1)).
Definition term52 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => ~ ((x0 y0) = x1).
Definition term16 (x0 : ind -> ind) := ((forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1)))) -> exists y0 : ind, (forall y1 : ind, forall y2 : ind, ((x0 y1) = (x0 y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((x0 y1) = y0)).
Definition term192 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term159 (x0 : ind -> ind) (x1 : ind) := fun y0 : ind => (fun y1 : ind => (~ ((x0 x1) = (x0 y1))) /\ (x1 = y1)) y0.
Definition term215 (x0 : ind -> ind) := exists y0 : ind -> ind, forall y1 : ind, (x0 (y0 y1)) = y1.
Definition term311 (x0 : ind) (x1 : ind) (x2 : ind) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term210 (x0 : ind -> ind) (x1 : ind -> ind) := fun y0 : ind => (x0 (x1 y0)) = y0.
Definition term225 (x0 : ind -> ind) := exists y0 : ind, (fun y1 : ind => exists y2 : ind, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) \/ ((~ ((x0 y1) = (x0 y2))) /\ (y1 = y2))) y0.
Definition term182 (x0 : ind -> ind) := exists y0 : ind, (fun y1 : ind => exists y2 : ind, (~ ((x0 y1) = (x0 y2))) /\ (y1 = y2)) y0.
Definition term177 (x0 : ind -> ind) := exists y0 : ind, (fun y1 : ind => exists y2 : ind, ((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) y0.
Definition term94 (x0 : ind -> ind) := exists y0 : ind, (fun y1 : ind => forall y2 : ind, ~ (y1 = (x0 y2))) y0.
Definition term43 (x0 : ind -> ind) := exists y0 : ind, (fun y1 : ind => forall y2 : ind, ~ ((x0 y2) = y1)) y0.
Definition term79 (x0 : ind) (x1 : ind -> ind) := forall y0 : ind, ~ (x0 = (x1 y0)).
Definition term300 (x0 : ind -> ind) (x1 : ind -> ind) (x2 : ind) := ~ ((x0 (x1 x2)) = x2).
Definition term230 (x0 : ind -> ind) (x1 : ind) := or (exists y0 : ind, (((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) \/ ((~ ((x0 x1) = (x0 y0))) /\ (x1 = y0))).
Definition term158 (x0 : ind -> ind) (x1 : ind) := or (exists y0 : ind, ((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))).
Definition term328 (x0 : ind) (x1 : ind -> ind) (x2 : ind) := (x0 = (x1 x2)) -> False.
Definition term71 (x0 : ind -> Prop) := forall y0 : ind, ~ (x0 y0).
Definition term213 (x0 : ind -> ind) := fun y0 : ind -> ind => forall y1 : ind, (fun y2 : ind => fun y3 : ind => (x0 y3) = y2) y1 (y0 y1).
Definition term67 (x0 : ind -> ind) (x1 : ind) := forall y0 : ind, (~ ((x0 x1) = (x0 y0))) \/ (x1 = y0).
Definition term11 (x0 : ind -> ind) := (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) -> y0 = y1) /\ (~ (forall y0 : ind, exists y1 : ind, y0 = (x0 y1))).
Definition term116 (x0 : ind -> ind) := fun y0 : ind => exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1)).
Definition term90 (x0 : ind -> ind) := (forall y0 : ind, forall y1 : ind, (~ ((x0 y0) = (x0 y1))) \/ (y0 = y1)) /\ (exists y0 : ind, (fun y1 : ind => forall y2 : ind, ~ (y1 = (x0 y2))) y0).
Definition term30 (x0 : ind -> ind) := (forall y0 : ind, forall y1 : ind, ((x0 y0) = (x0 y1)) = (y0 = y1)) /\ (exists y0 : ind, (fun y1 : ind => forall y2 : ind, ~ ((x0 y2) = y1)) y0).
Definition term243 (x0 : ind) (x1 : ind -> ind) := @eq Prop ((exists y0 : ind, (((x1 x0) = (x1 y0)) /\ (~ (x0 = y0))) \/ ((~ ((x1 x0) = (x1 y0))) /\ (x0 = y0))) \/ (exists y0 : ind -> ind, forall y1 : ind, (x1 (y0 y1)) = y1)).
Definition term242 (x0 : ind) (x1 : ind -> ind) := @eq Prop ((exists y0 : ind, (fun y1 : ind => (((x1 x0) = (x1 y1)) /\ (~ (x0 = y1))) \/ ((~ ((x1 x0) = (x1 y1))) /\ (x0 = y1))) y0) \/ (exists y0 : ind -> ind, forall y1 : ind, (x1 (y0 y1)) = y1)).
Definition term228 (x0 : ind -> ind) := @eq Prop ((exists y0 : ind, exists y1 : ind, (((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ ((~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))) \/ (exists y0 : ind -> ind, forall y1 : ind, (x0 (y0 y1)) = y1)).
Definition term227 (x0 : ind -> ind) := @eq Prop ((exists y0 : ind, (fun y1 : ind => exists y2 : ind, (((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) \/ ((~ ((x0 y1) = (x0 y2))) /\ (y1 = y2))) y0) \/ (exists y0 : ind -> ind, forall y1 : ind, (x0 (y0 y1)) = y1)).
Definition term190 (x0 : ind -> ind) (x1 : ind) := @eq Prop ((exists y0 : ind, ((x0 x1) = (x0 y0)) /\ (~ (x1 = y0))) \/ (exists y0 : ind, (~ ((x0 x1) = (x0 y0))) /\ (x1 = y0))).
Definition term189 (x0 : ind -> ind) (x1 : ind) := @eq Prop ((exists y0 : ind, (fun y1 : ind => ((x0 x1) = (x0 y1)) /\ (~ (x1 = y1))) y0) \/ (exists y0 : ind, (fun y1 : ind => (~ ((x0 x1) = (x0 y1))) /\ (x1 = y1)) y0)).
Definition term188 (x0 : ind -> ind) := @eq Prop ((exists y0 : ind, exists y1 : ind, ((x0 y0) = (x0 y1)) /\ (~ (y0 = y1))) \/ (exists y0 : ind, exists y1 : ind, (~ ((x0 y0) = (x0 y1))) /\ (y0 = y1))).
Definition term187 (x0 : ind -> ind) := @eq Prop ((exists y0 : ind, (fun y1 : ind => exists y2 : ind, ((x0 y1) = (x0 y2)) /\ (~ (y1 = y2))) y0) \/ (exists y0 : ind, (fun y1 : ind => exists y2 : ind, (~ ((x0 y1) = (x0 y2))) /\ (y1 = y2)) y0)).
