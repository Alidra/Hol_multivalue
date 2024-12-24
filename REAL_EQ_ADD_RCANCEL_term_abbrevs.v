Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : real) (x1 : real) := forall y0 : real, ((real_add x0 x1) = (real_add x0 y0)) = (x1 = y0).
Definition term127 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) x1.
Definition term300 (x0 : real) (x1 : real) (x2 : real) := @eq Prop (~ ((real_add x0 x2) = (real_add x1 x2))).
Definition term32 (x0 : real -> Prop) := ~ (all x0).
Definition term347 := (~ False) -> False.
Definition term101 (x0 : real) (x1 : real) := (exists y0 : real, (real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1)).
Definition term11 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)).
Definition term26 (x0 : real) (x1 : real) := forall y0 : real, ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1).
Definition term193 (x0 : real) := (exists y0 : real, exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ (exists y0 : real, exists y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)).
Definition term178 := (exists y0 : real, exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ (exists y0 : real, exists y1 : real, exists y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)).
Definition term164 := (exists y0 : real, exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ (exists y0 : real, exists y1 : real, (exists y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)).
Definition term108 (x0 : real) (x1 : real) (x2 : real) := and ((fun y0 : real => ~ ((real_add x0 y0) = (real_add x1 y0))) x2).
Definition term134 (x0 : real) := fun y0 : real => (fun y1 : real => (exists y2 : real, (real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0.
Definition term72 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) /\ (~ (x0 = x1))) y0.
Definition term119 (x0 : real) (x1 : real) := (exists y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1).
Definition term104 (x0 : real) (x1 : real) := (exists y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) /\ (x0 = x1).
Definition term330 (x0 : real) (x1 : real) (x2 : real) := (((real_add x2 x1) = (real_add x0 x1)) /\ ((real_add x2 x1) = (real_add x1 x2))) -> (real_add x0 x1) = (real_add x1 x2).
Definition term321 (x0 : Prop) := ~ (~ x0).
Definition term288 := and (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))).
Definition term266 (x0 : real) := and (forall y0 : real, forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))).
Definition term39 (x0 : real) (x1 : real) := fun y0 : real => (((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) \/ ((~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1)).
Definition term61 (x0 : real) (x1 : real) := fun y0 : real => (~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1).
Definition term229 (x0 : real) (x1 : real) := fun y0 : real => (~ ((real_add x0 x1) = (real_add x0 y0))) \/ (x1 = y0).
Definition term116 (x0 : real) (x1 : real) := exists y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0)).
Definition term244 (x0 : real) (x1 : real) := and (forall y0 : real, ((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0))).
Definition term320 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term60 (x0 : real) (x1 : real) := fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1)).
Definition term278 (x0 : real) := and ((fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) x0).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term230 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0))) x2.
Definition term203 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)) x1.
Definition term199 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) x1.
Definition term139 (x0 : real) := fun y0 : real => (fun y1 : real => (exists y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0.
Definition term77 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) /\ (x0 = x1)) y0.
Definition term287 := and (forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y2) = (real_add y1 y3)) \/ (~ (y2 = y3))) y0).
Definition term265 (x0 : real) := and (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_add x0 y1) = (real_add x0 y2)) \/ (~ (y1 = y2))) y0).
Definition term243 (x0 : real) (x1 : real) := and (forall y0 : real, (fun y1 : real => ((real_add x0 x1) = (real_add x0 y1)) \/ (~ (x1 = y1))) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term326 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term120 (x0 : real) (x1 : real) := ((exists y0 : real, (real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) \/ ((exists y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1)).
Definition term98 (x0 : real) (x1 : real) := exists y0 : real, (real_add x0 y0) = (real_add x1 y0).
Definition term34 (x0 : real) (x1 : real) := ~ (forall y0 : real, ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1)).
Definition term79 (x0 : real) (x1 : real) := exists y0 : real, (~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1).
Definition term114 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0.
Definition term36 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1)) x2.
Definition term249 (x0 : real) := fun y0 : real => (forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1)).
Definition term329 (x0 : real) (x1 : real) (x2 : real) := ((real_add x2 x1) = (real_add x0 x1)) /\ ((real_add x2 x1) = (real_add x1 x2)).
Definition term297 (x0 : real) (x1 : real) := (fun y0 : real => ~ ((real_add y0 x0) = (real_add x1 x0))) x1.
Definition term346 (x0 : real) (x1 : real) := (x0 = x1) -> False.
Definition term190 (x0 : real) := or ((fun y0 : real => exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) x0).
Definition term150 (x0 : real) := or ((fun y0 : real => exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) x0).
Definition term83 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term17 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term110 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => ~ ((real_add x1 y0) = (real_add x2 y0))) x0) /\ (x1 = x2).
Definition term87 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 y0) = (real_add x1 y0).
Definition term121 (x0 : real) := fun y0 : real => ((exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ ((exists y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)).
Definition term292 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, (~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2)).
Definition term270 (x0 : real) := (forall y0 : real, forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, (~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1)).
Definition term294 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1.
Definition term31 (x0 : real) (x1 : real) (x2 : real) := (((real_add x1 x0) = (real_add x2 x0)) /\ (~ (x1 = x2))) \/ ((~ ((real_add x1 x0) = (real_add x2 x0))) /\ (x1 = x2)).
Definition term314 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term274 := (forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y2) = (real_add y1 y3)) \/ (~ (y2 = y3))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, (~ ((real_add y1 y2) = (real_add y1 y3))) \/ (y2 = y3)) y0).
Definition term252 (x0 : real) := (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_add x0 y1) = (real_add x0 y2)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ ((real_add x0 y1) = (real_add x0 y2))) \/ (y1 = y2)) y0).
Definition term227 (x0 : real) (x1 : real) := (forall y0 : real, (fun y1 : real => ((real_add x0 x1) = (real_add x0 y1)) \/ (~ (x1 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ ((real_add x0 x1) = (real_add x0 y1))) \/ (x1 = y1)) y0).
Definition term209 (x0 : real) (x1 : real) := ((fun y0 : real => exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) x1) \/ ((fun y0 : real => exists y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)) x1).
Definition term343 (x0 : real) (x1 : real) (x2 : real) := imp ((real_add x1 x0) = (real_add x1 x2)).
Definition term16 (x0 : real) := fun y0 : real => (real_add x0 y0) = (real_add y0 x0).
Definition term299 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((fun y0 : real => ~ ((real_add y0 x1) = (real_add x0 x1))) x2).
Definition term298 (x0 : real) (x1 : real) := ~ ((real_add x0 x1) = (real_add x0 x1)).
Definition term111 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) /\ (x0 = x1).
Definition term303 (x0 : Prop) := (~ x0) -> x0.
Definition term5 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False.
Definition term316 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term289 := fun y0 : real => (fun y1 : real => forall y2 : real, forall y3 : real, (~ ((real_add y1 y2) = (real_add y1 y3))) \/ (y2 = y3)) y0.
Definition term284 := fun y0 : real => (fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y2) = (real_add y1 y3)) \/ (~ (y2 = y3))) y0.
Definition term267 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : real, (~ ((real_add x0 y1) = (real_add x0 y2))) \/ (y1 = y2)) y0.
Definition term262 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : real, ((real_add x0 y1) = (real_add x0 y2)) \/ (~ (y1 = y2))) y0.
Definition term62 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) x2.
Definition term318 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term312 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term140 (x0 : real) := exists y0 : real, (fun y1 : real => (exists y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0.
Definition term135 (x0 : real) := exists y0 : real, (fun y1 : real => (exists y2 : real, (real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0.
Definition term97 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0.
Definition term78 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) /\ (x0 = x1)) y0.
Definition term73 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) /\ (~ (x0 = x1))) y0.
Definition term291 := forall y0 : real, forall y1 : real, forall y2 : real, (~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2).
Definition term286 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2)).
Definition term269 (x0 : real) := forall y0 : real, forall y1 : real, (~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1).
Definition term264 (x0 : real) := forall y0 : real, forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1)).
Definition term221 := forall y0 : real, forall y1 : real, forall y2 : real, (((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) /\ ((~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2)).
Definition term219 (x0 : real) := forall y0 : real, forall y1 : real, (((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) /\ ((~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1)).
Definition term28 (x0 : real) := forall y0 : real, forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0).
Definition term24 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2).
Definition term22 (x0 : real) := forall y0 : real, forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) = (y0 = y1).
Definition term10 := forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term1 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1).
Definition term313 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term217 (x0 : real) (x1 : real) := forall y0 : real, (((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0))) /\ ((~ ((real_add x0 x1) = (real_add x0 y0))) \/ (x1 = y0)).
Definition term64 (x0 : real) (x1 : real) (x2 : real) := or ((fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) x2).
Definition term177 := exists y0 : real, exists y1 : real, exists y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1).
Definition term175 (x0 : real) := exists y0 : real, exists y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0).
Definition term170 := exists y0 : real, exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1)).
Definition term168 (x0 : real) := exists y0 : real, exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0)).
Definition term163 := exists y0 : real, exists y1 : real, (exists y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1).
Definition term158 := exists y0 : real, exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1)).
Definition term53 := exists y0 : real, exists y1 : real, exists y2 : real, (((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ ((~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)).
Definition term47 (x0 : real) := exists y0 : real, exists y1 : real, (((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ ((~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)).
Definition term223 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term12 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False.
Definition term345 (x0 : real) (x1 : real) := (~ (x0 = x1)) -> x0 = x1.
Definition term202 (x0 : real) := or (exists y0 : real, (fun y1 : real => exists y2 : real, ((real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0).
Definition term184 := or (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ((real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0).
Definition term159 := or (exists y0 : real, (fun y1 : real => exists y2 : real, (exists y3 : real, (real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0).
Definition term137 (x0 : real) := or (exists y0 : real, (fun y1 : real => (exists y2 : real, (real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0).
Definition term75 (x0 : real) (x1 : real) := or (exists y0 : real, (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) /\ (~ (x0 = x1))) y0).
Definition term122 (x0 : real) := exists y0 : real, ((exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ ((exists y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)).
Definition term40 (x0 : real) (x1 : real) := exists y0 : real, (((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) \/ ((~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1)).
Definition term125 (x0 : real) := fun y0 : real => (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0)).
Definition term310 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term30 (x0 : real) (x1 : real) (x2 : real) := ~ (((real_add x1 x0) = (real_add x2 x0)) = (x1 = x2)).
Definition term15 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> ~ (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)).
Definition term19 (x0 : real) (x1 : real) := fun y0 : real => ((real_add x0 x1) = (real_add x0 y0)) = (x1 = y0).
Definition term48 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y3) = (real_add y2 y3)) = (y1 = y2)) y0).
Definition term42 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_add x0 y2) = (real_add y1 y2)) = (x0 = y1)) y0).
Definition term35 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) = (x0 = x1)) y0).
Definition term151 (x0 : real) := (fun y0 : real => exists y1 : real, (exists y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)) x0.
Definition term149 (x0 : real) := (fun y0 : real => exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) x0.
Definition term231 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 x1) = (real_add x0 x2)) \/ (~ (x1 = x2)).
Definition term166 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, (real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))).
Definition term165 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) /\ (~ (x0 = x1))).
Definition term106 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ~ ((real_add x0 y0) = (real_add x1 y0))) x2.
Definition term51 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y3) = (real_add y2 y3)) = (y1 = y2)) y0).
Definition term45 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_add x0 y2) = (real_add y1 y2)) = (x0 = y1)) y0).
Definition term283 := @eq Prop (forall y0 : real, (forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) /\ (forall y1 : real, forall y2 : real, (~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2))).
Definition term282 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y2) = (real_add y1 y3)) \/ (~ (y2 = y3))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, (~ ((real_add y1 y2) = (real_add y1 y3))) \/ (y2 = y3)) y0)).
Definition term261 (x0 : real) := @eq Prop (forall y0 : real, (forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1))).
Definition term260 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add x0 y1) = (real_add x0 y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((real_add x0 y1) = (real_add x0 y2))) \/ (y1 = y2)) y0)).
Definition term239 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, (((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0))) /\ ((~ ((real_add x0 x1) = (real_add x0 y0))) \/ (x1 = y0))).
Definition term238 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ((real_add x0 x1) = (real_add x0 y1)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : real => (~ ((real_add x0 x1) = (real_add x0 y1))) \/ (x1 = y1)) y0)).
Definition term301 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term167 (x0 : real) := fun y0 : real => exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0)).
Definition term147 := fun y0 : real => exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1)).
Definition term218 (x0 : real) := fun y0 : real => forall y1 : real, (((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) /\ ((~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1)).
Definition term103 (x0 : real) (x1 : real) := exists y0 : real, ((fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) /\ (x0 = x1).
Definition term8 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False.
Definition term192 (x0 : real) := ((fun y0 : real => exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) x0) \/ ((fun y0 : real => exists y1 : real, exists y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)) x0).
Definition term152 (x0 : real) := ((fun y0 : real => exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) x0) \/ ((fun y0 : real => exists y1 : real, (exists y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)) x0).
Definition term25 (x0 : real) (x1 : real) := fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1).
Definition term339 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ (~ ((real_add x1 x0) = (real_add x1 x2)))).
Definition term88 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term56 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term142 (x0 : real) := (exists y0 : real, (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ (exists y0 : real, (exists y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)).
Definition term80 (x0 : real) (x1 : real) := (exists y0 : real, ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) \/ (exists y0 : real, (~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1)).
Definition term41 (x0 : real) := ~ (forall y0 : real, forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0)).
Definition term9 := ~ (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)).
Definition term3 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)).
Definition term233 (x0 : real) (x1 : real) (x2 : real) := and (((real_add x0 x1) = (real_add x0 x2)) \/ (~ (x1 = x2))).
Definition term342 (x0 : real) (x1 : real) (x2 : real) := imp (~ (~ ((real_add x1 x0) = (real_add x1 x2)))).
Definition term258 (x0 : real) (x1 : real) := ((fun y0 : real => forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) x1) /\ ((fun y0 : real => forall y1 : real, (~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1)) x1).
Definition term234 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (~ ((real_add x0 x1) = (real_add x0 y0))) \/ (x1 = y0)) x2.
Definition term74 (x0 : real) (x1 : real) := exists y0 : real, ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1)).
Definition term307 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term204 (x0 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, (~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0.
Definition term200 (x0 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, ((real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0.
Definition term186 := fun y0 : real => (fun y1 : real => exists y2 : real, exists y3 : real, (~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0.
Definition term182 := fun y0 : real => (fun y1 : real => exists y2 : real, exists y3 : real, ((real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0.
Definition term161 := fun y0 : real => (fun y1 : real => exists y2 : real, (exists y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0.
Definition term156 := fun y0 : real => (fun y1 : real => exists y2 : real, (exists y3 : real, (real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0.
Definition term331 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x0 x1) = (real_add x1 x2))) -> (real_add x0 x1) = (real_add x1 x2).
Definition term57 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term333 (x0 : real) (x1 : real) (x2 : real) := ((real_add x2 x1) = (real_add x1 x0)) /\ ((real_add x2 x1) = (real_add x1 x2)).
Definition term317 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term248 (x0 : real) (x1 : real) := (forall y0 : real, ((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0))) /\ (forall y0 : real, (~ ((real_add x0 x1) = (real_add x0 y0))) \/ (x1 = y0)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term50 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) x0).
Definition term46 (x0 : real) := fun y0 : real => exists y1 : real, (((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ ((~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)).
Definition term102 (x0 : real) (x1 : real) := or ((exists y0 : real, (real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))).
Definition term216 (x0 : real) (x1 : real) := fun y0 : real => (((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0))) /\ ((~ ((real_add x0 x1) = (real_add x0 y0))) \/ (x1 = y0)).
Definition term302 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x0 x2) = (real_add x1 x2))) -> (real_add x0 x2) = (real_add x1 x2).
Definition term240 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ((real_add x0 x1) = (real_add x0 y1)) \/ (~ (x1 = y1))) y0.
Definition term305 (x0 : real) (x1 : real) := ~ ((real_add x1 x0) = (real_add x0 x1)).
Definition term6 := (((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False.
Definition term235 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x0 x1) = (real_add x0 x2))) \/ (x1 = x2).
Definition term155 := @eq Prop (exists y0 : real, (exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ (exists y1 : real, (exists y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1))).
Definition term154 := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, (exists y3 : real, (real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (exists y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0)).
Definition term133 (x0 : real) := @eq Prop (exists y0 : real, ((exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ ((exists y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0))).
Definition term132 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => (exists y2 : real, (real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0) \/ ((fun y1 : real => (exists y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0)).
Definition term113 (x0 : real) (x1 : real) := @eq Prop (exists y0 : real, (~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1)).
Definition term112 (x0 : real) (x1 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) /\ (x0 = x1)).
Definition term95 (x0 : real) (x1 : real) := @eq Prop (exists y0 : real, ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))).
Definition term94 (x0 : real) (x1 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) /\ (~ (x0 = x1))).
Definition term71 (x0 : real) (x1 : real) := @eq Prop (exists y0 : real, (((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) \/ ((~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1))).
Definition term70 (x0 : real) (x1 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) /\ (~ (x0 = x1))) y0) \/ ((fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) /\ (x0 = x1)) y0)).
Definition term254 (x0 : real) := fun y0 : real => forall y1 : real, (~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1).
Definition term27 (x0 : real) := fun y0 : real => forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0).
Definition term21 (x0 : real) := fun y0 : real => forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) = (y0 = y1).
Definition term18 := fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term109 (x0 : real) (x1 : real) (x2 : real) := and (~ ((real_add x0 x2) = (real_add x1 x2))).
Definition term33 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term224 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) x2) \/ ((fun y0 : real => (~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1)) x2).
Definition term37 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1)) x2).
Definition term293 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term271 := fun y0 : real => (forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) /\ (forall y1 : real, forall y2 : real, (~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2)).
Definition term115 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0.
Definition term2 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> False.
Definition term246 (x0 : real) (x1 : real) := forall y0 : real, (fun y1 : real => (~ ((real_add x0 x1) = (real_add x0 y1))) \/ (x1 = y1)) y0.
Definition term241 (x0 : real) (x1 : real) := forall y0 : real, (fun y1 : real => ((real_add x0 x1) = (real_add x0 y1)) \/ (~ (x1 = y1))) y0.
Definition term325 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term281 := fun y0 : real => ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y2) = (real_add y1 y3)) \/ (~ (y2 = y3))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, (~ ((real_add y1 y2) = (real_add y1 y3))) \/ (y2 = y3)) y0).
Definition term259 (x0 : real) := fun y0 : real => ((fun y1 : real => forall y2 : real, ((real_add x0 y1) = (real_add x0 y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((real_add x0 y1) = (real_add x0 y2))) \/ (y1 = y2)) y0).
Definition term232 (x0 : real) (x1 : real) (x2 : real) := and ((fun y0 : real => ((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0))) x2).
Definition term90 (x0 : real) (x1 : real) (x2 : real) := and ((fun y0 : real => (real_add x0 y0) = (real_add x1 y0)) x2).
Definition term311 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term309 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term136 (x0 : real) := exists y0 : real, (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0)).
Definition term236 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => ((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0))) x2) /\ ((fun y0 : real => (~ ((real_add x0 x1) = (real_add x0 y0))) \/ (x1 = y0)) x2).
Definition term7 := (((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False) -> ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False.
Definition term256 (x0 : real) (x1 : real) := and ((fun y0 : real => forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) x1).
Definition term304 (x0 : real) (x1 : real) := (~ ((real_add x1 x0) = (real_add x0 x1))) -> (real_add x1 x0) = (real_add x0 x1).
Definition term257 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1)) x1.
Definition term255 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) x1.
Definition term43 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0)) x1.
Definition term323 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term105 (x0 : real) (x1 : real) := fun y0 : real => ~ ((real_add x0 y0) = (real_add x1 y0)).
Definition term296 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ~ ((real_add y0 x1) = (real_add x0 x1))) x2.
Definition term65 (x0 : real) (x1 : real) (x2 : real) := or (((real_add x1 x0) = (real_add x2 x0)) /\ (~ (x1 = x2))).
Definition term131 (x0 : real) := fun y0 : real => ((fun y1 : real => (exists y2 : real, (real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0) \/ ((fun y1 : real => (exists y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0).
Definition term69 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) /\ (~ (x0 = x1))) y0) \/ ((fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) /\ (x0 = x1)) y0).
Definition term349 (x0 : real) (x1 : real) := ((real_add x0 x1) = (real_add x0 x1)) -> False.
Definition term89 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add x0 y0) = (real_add x1 y0)) x2.
Definition term86 (x0 : real) (x1 : real) := (exists y0 : real, (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) /\ (~ (x0 = x1)).
Definition term198 (x0 : real) := exists y0 : real, ((fun y1 : real => exists y2 : real, ((real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0) \/ ((fun y1 : real => exists y2 : real, (~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0).
Definition term180 := exists y0 : real, ((fun y1 : real => exists y2 : real, exists y3 : real, ((real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, exists y3 : real, (~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0).
Definition term145 := exists y0 : real, ((fun y1 : real => exists y2 : real, (exists y3 : real, (real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (exists y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0).
Definition term123 (x0 : real) := exists y0 : real, ((fun y1 : real => (exists y2 : real, (real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0) \/ ((fun y1 : real => (exists y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0).
Definition term58 (x0 : real) (x1 : real) := exists y0 : real, ((fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) /\ (~ (x0 = x1))) y0) \/ ((fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) /\ (x0 = x1)) y0).
Definition term337 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ ((real_add x1 x0) = (real_add x1 x2))).
Definition term195 := fun y0 : real => (exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ (exists y1 : real, exists y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)).
Definition term332 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x0 x1) = (real_add x1 x2)).
Definition term84 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term215 (x0 : real) (x1 : real) (x2 : real) := (((real_add x0 x1) = (real_add x0 x2)) \/ (~ (x1 = x2))) /\ ((~ ((real_add x0 x1) = (real_add x0 x2))) \/ (x1 = x2)).
Definition term96 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0.
Definition term93 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) /\ (~ (x0 = x1)).
Definition term338 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ ((real_add x0 x1) = (real_add x0 x2))) \/ (x1 = x2)).
Definition term174 (x0 : real) := fun y0 : real => exists y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0).
Definition term148 := fun y0 : real => exists y1 : real, (exists y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1).
Definition term276 := fun y0 : real => forall y1 : real, forall y2 : real, (~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2).
Definition term275 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2)).
Definition term220 := fun y0 : real => forall y1 : real, forall y2 : real, (((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) /\ ((~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2)).
Definition term29 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1).
Definition term23 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2).
Definition term44 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0)) x1).
Definition term176 := fun y0 : real => exists y1 : real, exists y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1).
Definition term169 := fun y0 : real => exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1)).
Definition term52 := fun y0 : real => exists y1 : real, exists y2 : real, (((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ ((~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := ((real_add x1 x0) = (real_add x2 x0)) /\ (~ (x1 = x2)).
Definition term128 (x0 : real) (x1 : real) := or ((fun y0 : real => (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) x1).
Definition term272 := forall y0 : real, (forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) /\ (forall y1 : real, forall y2 : real, (~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2)).
Definition term250 (x0 : real) := forall y0 : real, (forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((real_add x0 y0) = (real_add x0 y1))) \/ (y0 = y1)).
Definition term247 (x0 : real) (x1 : real) := forall y0 : real, (~ ((real_add x0 x1) = (real_add x0 y0))) \/ (x1 = y0).
Definition term328 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term319 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term315 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term129 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)) x1.
Definition term340 (x0 : real) (x1 : real) (x2 : real) := (~ (~ ((real_add x0 x1) = (real_add x0 x2)))) -> x1 = x2.
Definition term117 (x0 : real) (x1 : real) := and (exists y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0).
Definition term99 (x0 : real) (x1 : real) := and (exists y0 : real, (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0).
Definition term336 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x1 x0) = (real_add x1 x2)).
Definition term290 := forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, (~ ((real_add y1 y2) = (real_add y1 y3))) \/ (y2 = y3)) y0.
Definition term285 := forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y2) = (real_add y1 y3)) \/ (~ (y2 = y3))) y0.
Definition term268 (x0 : real) := forall y0 : real, (fun y1 : real => forall y2 : real, (~ ((real_add x0 y1) = (real_add x0 y2))) \/ (y1 = y2)) y0.
Definition term263 (x0 : real) := forall y0 : real, (fun y1 : real => forall y2 : real, ((real_add x0 y1) = (real_add x0 y2)) \/ (~ (y1 = y2))) y0.
Definition term130 (x0 : real) (x1 : real) := ((fun y0 : real => (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) x1) \/ ((fun y0 : real => (exists y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)) x1).
Definition term324 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term185 (x0 : real) := (fun y0 : real => exists y1 : real, exists y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)) x0.
Definition term181 (x0 : real) := (fun y0 : real => exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) x0.
Definition term280 (x0 : real) := ((fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) x0) /\ ((fun y0 : real => forall y1 : real, forall y2 : real, (~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2)) x0).
Definition term13 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> ~ (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)).
Definition term107 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x0 x2) = (real_add x1 x2)).
Definition term118 (x0 : real) (x1 : real) := and (exists y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0))).
Definition term237 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => ((real_add x0 x1) = (real_add x0 y1)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : real => (~ ((real_add x0 x1) = (real_add x0 y1))) \/ (x1 = y1)) y0).
Definition term245 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => (~ ((real_add x0 x1) = (real_add x0 y1))) \/ (x1 = y1)) y0.
Definition term228 (x0 : real) (x1 : real) := fun y0 : real => ((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0)).
Definition term38 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) = (x0 = x1)) y0).
Definition term225 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term85 (x0 : real) (x1 : real) := exists y0 : real, ((fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) /\ (~ (x0 = x1)).
Definition term327 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term92 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => (real_add x1 y0) = (real_add x2 y0)) x0) /\ (~ (x1 = x2)).
Definition term222 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term126 (x0 : real) := fun y0 : real => (exists y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0).
Definition term334 (x0 : real) (x1 : real) (x2 : real) := (((real_add x2 x1) = (real_add x1 x0)) /\ ((real_add x2 x1) = (real_add x1 x2))) -> (real_add x1 x0) = (real_add x1 x2).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term306 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term322 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term212 (x0 : real) := exists y0 : real, (exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ (exists y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)).
Definition term196 := exists y0 : real, (exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ (exists y1 : real, exists y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)).
Definition term144 := exists y0 : real, (exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ (exists y1 : real, (exists y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)).
Definition term91 (x0 : real) (x1 : real) (x2 : real) := and ((real_add x0 x2) = (real_add x1 x2)).
Definition term308 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term210 (x0 : real) := fun y0 : real => ((fun y1 : real => exists y2 : real, ((real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0) \/ ((fun y1 : real => exists y2 : real, (~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0).
Definition term194 := fun y0 : real => ((fun y1 : real => exists y2 : real, exists y3 : real, ((real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, exists y3 : real, (~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0).
Definition term153 := fun y0 : real => ((fun y1 : real => exists y2 : real, (exists y3 : real, (real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (exists y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0).
Definition term348 (x0 : real) (x1 : real) := (~ ((real_add x0 x1) = (real_add x0 x1))) -> (real_add x0 x1) = (real_add x0 x1).
Definition term138 (x0 : real) := or (exists y0 : real, (exists y1 : real, (real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))).
Definition term76 (x0 : real) (x1 : real) := or (exists y0 : real, ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))).
Definition term279 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (~ ((real_add y0 y1) = (real_add y0 y2))) \/ (y1 = y2)) x0.
Definition term277 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) \/ (~ (y1 = y2))) x0.
Definition term49 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) x0.
Definition term191 (x0 : real) := or (exists y0 : real, exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))).
Definition term171 := or (exists y0 : real, exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))).
Definition term160 := or (exists y0 : real, exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term4 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y1) = (real_add y0 y2)) = (y1 = y2)) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> False.
Definition term100 (x0 : real) (x1 : real) := and (exists y0 : real, (real_add x0 y0) = (real_add x1 y0)).
Definition term295 (x0 : real) (x1 : real) := fun y0 : real => ~ ((real_add y0 x1) = (real_add x0 x1)).
Definition term211 (x0 : real) := fun y0 : real => (exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ (exists y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0)).
Definition term143 := fun y0 : real => (exists y1 : real, (exists y2 : real, (real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ (exists y1 : real, (exists y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1)).
Definition term242 (x0 : real) (x1 : real) := forall y0 : real, ((real_add x0 x1) = (real_add x0 y0)) \/ (~ (x1 = y0)).
Definition term273 := forall y0 : real, ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_add y1 y2) = (real_add y1 y3)) \/ (~ (y2 = y3))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, (~ ((real_add y1 y2) = (real_add y1 y3))) \/ (y2 = y3)) y0).
Definition term251 (x0 : real) := forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add x0 y1) = (real_add x0 y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((real_add x0 y1) = (real_add x0 y2))) \/ (y1 = y2)) y0).
Definition term226 (x0 : real) (x1 : real) := forall y0 : real, ((fun y1 : real => ((real_add x0 x1) = (real_add x0 y1)) \/ (~ (x1 = y1))) y0) /\ ((fun y1 : real => (~ ((real_add x0 x1) = (real_add x0 y1))) \/ (x1 = y1)) y0).
Definition term141 (x0 : real) := exists y0 : real, (exists y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0).
Definition term173 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1)).
Definition term172 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) /\ (x0 = x1)).
Definition term344 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 x1) = (real_add x0 x2)) -> x1 = x2.
Definition term197 (x0 : real) := (exists y0 : real, (fun y1 : real => exists y2 : real, ((real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0).
Definition term179 := (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ((real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, (~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0).
Definition term146 := (exists y0 : real, (fun y1 : real => exists y2 : real, (exists y3 : real, (real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (exists y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0).
Definition term124 (x0 : real) := (exists y0 : real, (fun y1 : real => (exists y2 : real, (real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0) \/ (exists y0 : real, (fun y1 : real => (exists y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0).
Definition term59 (x0 : real) (x1 : real) := (exists y0 : real, (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) /\ (~ (x0 = x1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) /\ (x0 = x1)) y0).
Definition term14 := imp (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1))).
Definition term253 (x0 : real) := fun y0 : real => forall y1 : real, ((real_add x0 y0) = (real_add x0 y1)) \/ (~ (y0 = y1)).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1)) x2.
Definition term208 (x0 : real) (x1 : real) := or ((fun y0 : real => exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) x1).
Definition term67 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x1 x0) = (real_add x2 x0))) /\ (x1 = x2).
Definition term341 (x0 : real) (x1 : real) (x2 : real) := ~ (~ ((real_add x1 x0) = (real_add x1 x2))).
Definition term335 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x1 x0) = (real_add x1 x2))) -> (real_add x1 x0) = (real_add x1 x2).
Definition term205 (x0 : real) := exists y0 : real, (fun y1 : real => exists y2 : real, (~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0.
Definition term201 (x0 : real) := exists y0 : real, (fun y1 : real => exists y2 : real, ((real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0.
Definition term187 := exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, (~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0.
Definition term183 := exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ((real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0.
Definition term162 := exists y0 : real, (fun y1 : real => exists y2 : real, (exists y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0.
Definition term157 := exists y0 : real, (fun y1 : real => exists y2 : real, (exists y3 : real, (real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0.
Definition term214 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, ((real_add x0 y0) = (real_add x1 y0)) /\ (~ (x0 = x1))) \/ (exists y0 : real, (~ ((real_add x0 y0) = (real_add x1 y0))) /\ (x0 = x1))).
Definition term213 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) /\ (~ (x0 = x1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) /\ (x0 = x1)) y0)).
Definition term207 (x0 : real) := @eq Prop ((exists y0 : real, exists y1 : real, ((real_add x0 y1) = (real_add y0 y1)) /\ (~ (x0 = y0))) \/ (exists y0 : real, exists y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) /\ (x0 = y0))).
Definition term206 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, ((real_add x0 y2) = (real_add y1 y2)) /\ (~ (x0 = y1))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ ((real_add x0 y2) = (real_add y1 y2))) /\ (x0 = y1)) y0)).
Definition term189 := @eq Prop ((exists y0 : real, exists y1 : real, exists y2 : real, ((real_add y0 y2) = (real_add y1 y2)) /\ (~ (y0 = y1))) \/ (exists y0 : real, exists y1 : real, exists y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) /\ (y0 = y1))).
Definition term188 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ((real_add y1 y3) = (real_add y2 y3)) /\ (~ (y1 = y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, (~ ((real_add y1 y3) = (real_add y2 y3))) /\ (y1 = y2)) y0)).
