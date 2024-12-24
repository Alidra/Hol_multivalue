Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term294 (x0 : real) (x1 : real) := fun y0 : real => ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0)).
Definition term270 (x0 : real) (x1 : real) := fun y0 : real => ((~ (y0 = x1)) /\ (~ (y0 = x0))) \/ (~ (real_le x1 y0)).
Definition term1 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term12 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term33 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, ~ ((@INSERT a0 y0 y1) = (@EMPTY a0))) x0.
Definition term427 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ ((~ (real_le y0 x0)) /\ (~ (real_le y0 x1)))) x2.
Definition term272 (x0 : real -> Prop) := ~ (all x0).
Definition term475 := (~ False) -> False.
Definition term84 (x0 : real) (x1 : real) := ((@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (~ ((@INSERT real x0 (@INSERT real x1 (@EMPTY real))) = (@EMPTY real)))) -> (real_le (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) (real_max x0 x1)) = (forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le y0 (real_max x0 x1)).
Definition term150 := (~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term108 (x0 : real) := forall y0 : real, (real_max x0 y0) = (sup (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))).
Definition term453 (x0 : real) := fun y0 : real => ~ (real_le y0 x0).
Definition term458 (x0 : real) (x1 : real) := @eq Prop (~ (real_le x0 x1)).
Definition term381 := fun y0 : real => exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))).
Definition term256 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) /\ (~ (x1 = x2)).
Definition term32 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) /\ (real_le x1 x2).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1))) x1.
Definition term384 := (exists y0 : real, exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) \/ (exists y0 : real, exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1)))).
Definition term359 (x0 : real) := (exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1))).
Definition term311 := (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))).
Definition term237 := and (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)).
Definition term193 (x0 : real) := and (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)).
Definition term137 (x0 : real) (x1 : real) (x2 : real) := imp (@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))).
Definition term49 (x0 : real) (x1 : real -> Prop) := real_le x0 (sup x1).
Definition term291 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ (real_le x1 y0)) x2.
Definition term267 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x1) \/ (y0 = x0)) /\ (real_le x1 y0)) x2.
Definition term120 (x0 : real) (x1 : real) := (x0 = x1) \/ False.
Definition term72 (x0 : real) (x1 : real) := ~ ((@INSERT real x0 (@INSERT real x1 (@EMPTY real))) = (@EMPTY real)).
Definition term313 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x1 x0) \/ (real_le x1 x2)).
Definition term217 := and (forall y0 : real, (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))).
Definition term173 (x0 : real) := and (forall y0 : real, (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term131 (x0 : real) (x1 : real) (x2 : real) := ((x2 = x0) \/ (x2 = x1)) /\ (real_le x1 x2).
Definition term227 (x0 : real) := and ((fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) x0).
Definition term341 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term470 (x0 : real) (x1 : real) := ~ ((x1 = x0) /\ (real_le x0 x1)).
Definition term50 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (real_le x1 y0).
Definition term253 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term409 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0)))) x1.
Definition term184 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1)) x1.
Definition term182 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) x1.
Definition term338 := or ((exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))).
Definition term431 (x0 : real) (x1 : real) := @eq Prop (((forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x0 y0))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0)))) \/ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ ((~ (real_le y0 x0)) /\ (~ (real_le y0 x1))))).
Definition term430 (x0 : real) (x1 : real) := @eq Prop (((forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x0 y0))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0)))) \/ (exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 x1)))) y0)).
Definition term320 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x0) \/ (y0 = x1)) -> (real_le y0 x0) \/ (real_le y0 x1)) x2.
Definition term213 := fun y0 : real => (fun y1 : real => (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) /\ (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3))) y0.
Definition term169 (x0 : real) := fun y0 : real => (fun y1 : real => (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) /\ (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2))) y0.
Definition term301 (x0 : real) := exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)).
Definition term279 (x0 : real) := exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1)).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term236 := and (forall y0 : real, (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0).
Definition term216 := and (forall y0 : real, (fun y1 : real => (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) /\ (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3))) y0).
Definition term192 (x0 : real) := and (forall y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0).
Definition term172 (x0 : real) := and (forall y0 : real, (fun y1 : real => (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) /\ (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2))) y0).
Definition term306 := fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)).
Definition term284 := fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2)).
Definition term147 (x0 : Prop) := (~ x0) -> False.
Definition term96 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) := ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) = (@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real))))) -> ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> (real_le x0 (real_max x1 x2)) = x3) -> ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> real_le x0 (real_max x1 x2)) = ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> x3).
Definition term318 (x0 : real) (x1 : real) := ~ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> (real_le y0 x0) \/ (real_le y0 x1)).
Definition term91 (x0 : real) (x1 : real) (x2 : real) := @IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real))).
Definition term288 (x0 : real) (x1 : real) (x2 : real) := ~ (((x2 = x0) \/ (x2 = x1)) /\ (real_le x1 x2)).
Definition term262 (x0 : real) (x1 : real) (x2 : real) := ~ (((x2 = x1) \/ (x2 = x0)) /\ (real_le x1 x2)).
Definition term419 (x0 : real) := fun y0 : real => ((forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))) \/ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0)))).
Definition term102 (x0 : real) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le y0 (real_max x0 x1).
Definition term446 (x0 : real) (x1 : real) := fun y0 : real => ((~ (y0 = x0)) \/ (~ (real_le x1 y0))) /\ ((~ (y0 = x1)) \/ (~ (real_le x1 y0))).
Definition term443 (x0 : real) (x1 : real) := fun y0 : real => ((~ (y0 = x1)) \/ (~ (real_le x1 y0))) /\ ((~ (y0 = x0)) \/ (~ (real_le x1 y0))).
Definition term396 (x0 : real) := or ((fun y0 : real => exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) x0).
Definition term356 (x0 : real) := or ((fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) x0).
Definition term251 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := (@IN real x1 (@INSERT real x0 (@INSERT real x2 (@EMPTY real)))) -> (real_le x1 (real_max x0 x2)) = ((real_le x1 x0) \/ (real_le x1 x2)).
Definition term78 (x0 : real) (x1 : real) := ((@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (~ ((@INSERT real x0 (@INSERT real x1 (@EMPTY real))) = (@EMPTY real)))) -> (real_le x1 (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))) = (exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x1 y0)).
Definition term63 (x0 : real) (x1 : real) := ((@FINITE real (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) /\ (~ ((@INSERT real x1 (@INSERT real x0 (@EMPTY real))) = (@EMPTY real)))) -> (real_le x1 (sup (@INSERT real x1 (@INSERT real x0 (@EMPTY real))))) = (exists y0 : real, (@IN real y0 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) /\ (real_le x1 y0)).
Definition term241 := (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)).
Definition term197 (x0 : real) := (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1)).
Definition term379 (x0 : real) := fun y0 : real => (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1))).
Definition term406 (x0 : real) := fun y0 : real => (fun y1 : real => (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) y0.
Definition term58 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0))) x1.
Definition term139 (x0 : real) (x1 : real) (x2 : real) := ((x1 = x0) \/ (x1 = x2)) -> (real_le x1 x0) \/ (real_le x1 x2).
Definition term465 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term121 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) \/ (x1 = x2).
Definition term223 := (forall y0 : real, (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3)) y0).
Definition term203 := (forall y0 : real, (fun y1 : real => (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) /\ (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> (real_le y3 y1) \/ (real_le y3 y2)) y0).
Definition term179 (x0 : real) := (forall y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0) /\ (forall y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2)) y0).
Definition term159 (x0 : real) := (forall y0 : real, (fun y1 : real => (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) /\ (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> (real_le y2 x0) \/ (real_le y2 y1)) y0).
Definition term376 (x0 : real) (x1 : real) := ((fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) x1) \/ ((fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1))) x1).
Definition term97 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) := ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> (real_le x0 (real_max x1 x2)) = x3) -> ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> real_le x0 (real_max x1 x2)) = ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> x3).
Definition term201 := forall y0 : real, ((forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term144 (x0 : real) := forall y0 : real, ((exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))) /\ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0)).
Definition term109 (x0 : real) := forall y0 : real, ((exists y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) /\ (real_le x0 y1)) /\ (exists y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) /\ (real_le y0 y1))) /\ (forall y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) -> (real_le y1 x0) \/ (real_le y1 y0)).
Definition term417 (x0 : real) (x1 : real) := ((forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x0 y0))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0)))) \/ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ ((~ (real_le y0 x0)) /\ (~ (real_le y0 x1)))).
Definition term3 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2))) x0.
Definition term459 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term142 (x0 : real) (x1 : real) := ((exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (real_le x0 y0)) /\ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (real_le x1 y0))) /\ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> (real_le y0 x0) \/ (real_le y0 x1)).
Definition term105 (x0 : real) (x1 : real) := ((exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x0 y0)) /\ (exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x1 y0))) /\ (forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> (real_le y0 x0) \/ (real_le y0 x1)).
Definition term468 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term461 (x0 : Prop) := (~ x0) -> x0.
Definition term314 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) /\ (~ (real_le x1 x2)).
Definition term370 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))) y0.
Definition term366 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) y0.
Definition term238 := fun y0 : real => (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3)) y0.
Definition term233 := fun y0 : real => (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0.
Definition term218 := fun y0 : real => (fun y1 : real => forall y2 : real, forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> (real_le y3 y1) \/ (real_le y3 y2)) y0.
Definition term174 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> (real_le y2 x0) \/ (real_le y2 y1)) y0.
Definition term225 := fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2).
Definition term224 := fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2).
Definition term200 := fun y0 : real => ((forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term138 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) \/ (x1 = x2)).
Definition term103 (x0 : real) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> (real_le y0 x0) \/ (real_le y0 x1).
Definition term40 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0).
Definition term429 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 x1)))) y0.
Definition term407 (x0 : real) := exists y0 : real, (fun y1 : real => (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) y0.
Definition term405 (x0 : real) (x1 : real) := (fun y0 : real => (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))) x1.
Definition term469 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term249 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term240 := forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2).
Definition term235 := forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2).
Definition term220 := forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1).
Definition term176 (x0 : real) := forall y0 : real, forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0).
Definition term146 := forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term113 := forall y0 : real, forall y1 : real, ((exists y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) /\ (real_le y0 y2)) /\ (exists y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) /\ (real_le y1 y2))) /\ (forall y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term112 := forall y0 : real, forall y1 : real, (real_max y0 y1) = (sup (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))).
Definition term27 (x0 : real) := forall y0 : real, forall y1 : real, (real_le (real_max x0 y0) y1) = ((real_le x0 y1) /\ (real_le y0 y1)).
Definition term20 (x0 : real) := forall y0 : real, forall y1 : real, (real_le y1 (real_max x0 y0)) = ((real_le y1 x0) \/ (real_le y1 y0)).
Definition term18 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term17 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term308 := or (~ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2))).
Definition term399 (x0 : real) := (exists y0 : real, (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))) \/ (exists y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0)))).
Definition term92 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) = y0) -> (y0 -> (real_le x0 (real_max x1 x2)) = y1) -> ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> real_le x0 (real_max x1 x2)) = (y0 -> y1)) x3.
Definition term440 := exists y0 : real, exists y1 : real, exists y2 : real, ((forall y3 : real, ((~ (y3 = y0)) /\ (~ (y3 = y1))) \/ (~ (real_le y0 y3))) \/ (forall y3 : real, ((~ (y3 = y0)) /\ (~ (y3 = y1))) \/ (~ (real_le y1 y3)))) \/ (((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1)))).
Definition term438 (x0 : real) := exists y0 : real, exists y1 : real, ((forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y0))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y0))) \/ (~ (real_le y0 y2)))) \/ (((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0)))).
Definition term382 := exists y0 : real, exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))).
Definition term336 := exists y0 : real, exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1))).
Definition term330 (x0 : real) := exists y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0))).
Definition term307 := exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)).
Definition term285 := exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2)).
Definition term264 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term82 (x0 : real) (x1 : real) := and (real_le (real_max x0 x1) (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term375 (x0 : real) (x1 : real) := or (forall y0 : real, ((~ (y0 = x1)) /\ (~ (y0 = x0))) \/ (~ (real_le x1 y0))).
Definition term408 (x0 : real) := or (exists y0 : real, (fun y1 : real => (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) y0).
Definition term390 := or (exists y0 : real, (fun y1 : real => exists y2 : real, (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) \/ (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3)))) y0).
Definition term368 (x0 : real) := or (exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) y0).
Definition term350 := or (exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) y0).
Definition term74 (x0 : real) (x1 : real) := real_le x0 (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))).
Definition term31 (x0 : real) (x1 : real) (x2 : real) := real_le (real_max x0 x1) x2.
Definition term85 (x0 : real) (x1 : real) := real_le (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) (real_max x0 x1).
Definition term60 (x0 : real) (x1 : real) := (real_le (real_max x0 x1) (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))) /\ (real_le (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) (real_max x0 x1)).
Definition term287 (x0 : real) (x1 : real) (x2 : real) := ((~ (x2 = x0)) /\ (~ (x2 = x1))) \/ (~ (real_le x1 x2)).
Definition term261 (x0 : real) (x1 : real) (x2 : real) := ((~ (x2 = x1)) /\ (~ (x2 = x0))) \/ (~ (real_le x1 x2)).
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> @FINITE a0 (@INSERT a0 x0 x1).
Definition term52 (x0 : real -> Prop) := forall y0 : real, ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le (sup x0) y0) = (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term45 (x0 : real -> Prop) := forall y0 : real, ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le y0 (sup x0)) = (exists y1 : real, (@IN real y1 x0) /\ (real_le y0 y1)).
Definition term59 (x0 : real) (x1 : real) := sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real))).
Definition term323 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ ((~ (real_le y0 x0)) /\ (~ (real_le y0 x1))).
Definition term79 (x0 : real) (x1 : real) := real_le x1 (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))).
Definition term433 (x0 : real) (x1 : real) (x2 : real) := ((forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x2))) \/ (~ (real_le x0 y0))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x2))) \/ (~ (real_le x2 y0)))) \/ (((x1 = x0) \/ (x1 = x2)) /\ ((~ (real_le x1 x0)) /\ (~ (real_le x1 x2)))).
Definition term141 (x0 : real) (x1 : real) := forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> (real_le y0 x0) \/ (real_le y0 x1).
Definition term104 (x0 : real) (x1 : real) := forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> (real_le y0 x0) \/ (real_le y0 x1).
Definition term456 (x0 : real) := ~ (real_le x0 x0).
Definition term99 (x0 : real) (x1 : real) (x2 : real) := ((@IN real x1 (@INSERT real x0 (@INSERT real x2 (@EMPTY real)))) -> (real_le x1 (real_max x0 x2)) = ((real_le x1 x0) \/ (real_le x1 x2))) -> ((@IN real x1 (@INSERT real x0 (@INSERT real x2 (@EMPTY real)))) -> real_le x1 (real_max x0 x2)) = ((@IN real x1 (@INSERT real x0 (@INSERT real x2 (@EMPTY real)))) -> (real_le x1 x0) \/ (real_le x1 x2)).
Definition term332 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> (real_le y3 y1) \/ (real_le y3 y2)) y0).
Definition term326 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> (real_le y2 x0) \/ (real_le y2 y1)) y0).
Definition term319 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) -> (real_le y1 x0) \/ (real_le y1 x1)) y0).
Definition term303 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3)) y0).
Definition term297 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2)) y0).
Definition term281 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0).
Definition term275 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0).
Definition term387 (x0 : real) := (fun y0 : real => exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) x0.
Definition term130 (x0 : real) (x1 : real) (x2 : real) := (@IN real x2 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x1 x2).
Definition term124 (x0 : real) (x1 : real) (x2 : real) := (@IN real x2 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) /\ (real_le x1 x2).
Definition term135 (x0 : real) (x1 : real) := (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (real_le x0 y0)) /\ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (real_le x1 y0)).
Definition term81 (x0 : real) (x1 : real) := (exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x0 y0)) /\ (exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x1 y0)).
Definition term434 (x0 : real) (x1 : real) := fun y0 : real => ((forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ (~ (real_le x1 y1)))) \/ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 x1)))) y0).
Definition term51 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (real_le (sup y0) y1) = (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) x0.
Definition term44 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (real_le y1 (sup y0)) = (exists y2 : real, (@IN real y2 y0) /\ (real_le y1 y2))) x0.
Definition term435 (x0 : real) (x1 : real) := fun y0 : real => ((forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ (~ (real_le x1 y1)))) \/ (((y0 = x0) \/ (y0 = x1)) /\ ((~ (real_le y0 x0)) /\ (~ (real_le y0 x1)))).
Definition term22 (x0 : real) (x1 : real) := forall y0 : real, (real_le y0 (real_max x0 x1)) = ((real_le y0 x0) \/ (real_le y0 x1)).
Definition term377 (x0 : real) (x1 : real) := (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x0 y0))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0))).
Definition term334 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> (real_le y3 y1) \/ (real_le y3 y2)) y0).
Definition term328 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> (real_le y2 x0) \/ (real_le y2 y1)) y0).
Definition term305 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3)) y0).
Definition term299 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2)) y0).
Definition term283 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0).
Definition term277 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0).
Definition term133 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ (real_le x1 y0).
Definition term127 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x1) \/ (y0 = x0)) /\ (real_le x1 y0).
Definition term426 (x0 : real) (x1 : real) := exists y0 : real, ((forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ (~ (real_le x1 y1)))) \/ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 x1)))) y0).
Definition term232 := @eq Prop (forall y0 : real, (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))).
Definition term231 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0) /\ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3)) y0)).
Definition term212 := @eq Prop (forall y0 : real, ((forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1))).
Definition term211 := @eq Prop (forall y0 : real, ((fun y1 : real => (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) /\ (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> (real_le y3 y1) \/ (real_le y3 y2)) y0)).
Definition term188 (x0 : real) := @eq Prop (forall y0 : real, (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))).
Definition term187 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0) /\ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2)) y0)).
Definition term168 (x0 : real) := @eq Prop (forall y0 : real, ((exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))) /\ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0))).
Definition term167 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) /\ (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> (real_le y2 x0) \/ (real_le y2 y1)) y0)).
Definition term87 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term68 (x0 : real) := (@FINITE real (@EMPTY real)) -> (@FINITE real (@INSERT real x0 (@EMPTY real))) = True.
Definition term432 (x0 : real) (x1 : real) (x2 : real) := ((forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x0 y0))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0)))) \/ ((fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ ((~ (real_le y0 x0)) /\ (~ (real_le y0 x1)))) x2).
Definition term123 (x0 : real) (x1 : real) (x2 : real) := and ((x1 = x0) \/ (x1 = x2)).
Definition term242 := and ((forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))).
Definition term198 (x0 : real) := and ((forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))).
Definition term134 (x0 : real) (x1 : real) := exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (real_le x1 y0).
Definition term128 (x0 : real) (x1 : real) := exists y0 : real, ((y0 = x1) \/ (y0 = x0)) /\ (real_le x1 y0).
Definition term80 (x0 : real) (x1 : real) := exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x1 y0).
Definition term75 (x0 : real) (x1 : real) := exists y0 : real, (@IN real y0 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) /\ (real_le x1 y0).
Definition term452 (x0 : real) (x1 : real) := (~ (x1 = x0)) \/ (~ (real_le x0 x1)).
Definition term472 (x0 : real) (x1 : real) := (x1 = x0) /\ (real_le x0 x1).
Definition term161 (x0 : real) := fun y0 : real => forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0).
Definition term16 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term467 (x0 : real) := (~ (real_le x0 x0)) -> real_le x0 x0.
Definition term247 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ~ ((@INSERT a0 x0 y0) = (@EMPTY a0))) x1.
Definition term398 (x0 : real) := ((fun y0 : real => exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) x0) \/ ((fun y0 : real => exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1)))) x0).
Definition term358 (x0 : real) := ((fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) x0) \/ ((fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))) x0).
Definition term56 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term451 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (y0 = x0)) \/ (~ (real_le x1 y0))) /\ ((~ (y0 = x1)) \/ (~ (real_le x1 y0)))) x2.
Definition term450 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (y0 = x1)) \/ (~ (real_le x1 y0))) /\ ((~ (y0 = x0)) \/ (~ (real_le x1 y0)))) x2.
Definition term10 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term69 (x0 : real) := @FINITE real (@INSERT real x0 (@EMPTY real)).
Definition term47 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le x1 (sup x0)) = (exists y0 : real, (@IN real y0 x0) /\ (real_le x1 y0)).
Definition term442 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term344 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term331 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term325 (x0 : real) := ~ (forall y0 : real, forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0)).
Definition term302 := ~ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)).
Definition term296 (x0 : real) := ~ (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1)).
Definition term280 := ~ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)).
Definition term274 (x0 : real) := ~ (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)).
Definition term248 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term149 := ~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1))).
Definition term115 (x0 : real) (x1 : real) (x2 : real -> Prop) := (x1 = x0) \/ (@IN real x1 x2).
Definition term143 (x0 : real) := fun y0 : real => ((exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))) /\ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0)).
Definition term107 (x0 : real) := fun y0 : real => ((exists y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) /\ (real_le x0 y1)) /\ (exists y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) /\ (real_le y0 y1))) /\ (forall y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) -> (real_le y1 x0) \/ (real_le y1 y0)).
Definition term152 := (((~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term185 (x0 : real) (x1 : real) := ((fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) x1) /\ ((fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1)) x1).
Definition term67 (x0 : real) (x1 : real) := (@FINITE real (@INSERT real x1 (@EMPTY real))) -> (@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) = True.
Definition term162 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))) x1.
Definition term420 (x0 : real) := exists y0 : real, ((forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))) \/ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0)))).
Definition term410 (x0 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((~ (real_le y2 x0)) /\ (~ (real_le y2 y1)))) y0.
Definition term392 := fun y0 : real => (fun y1 : real => exists y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((~ (real_le y3 y1)) /\ (~ (real_le y3 y2)))) y0.
Definition term388 := fun y0 : real => (fun y1 : real => exists y2 : real, (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) \/ (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3)))) y0.
Definition term352 := fun y0 : real => (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3))) y0.
Definition term348 := fun y0 : real => (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) y0.
Definition term194 (x0 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2)) y0.
Definition term189 (x0 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0.
Definition term422 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term340 := ((exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) \/ (exists y0 : real, exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1)))).
Definition term380 (x0 : real) := exists y0 : real, (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1))).
Definition term95 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) = x3) -> (x3 -> (real_le x0 (real_max x1 x2)) = x4) -> ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> real_le x0 (real_max x1 x2)) = (x3 -> x4).
Definition term343 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term258 (x0 : real) (x1 : real) (x2 : real) := or (~ ((x1 = x0) \/ (x1 = x2))).
Definition term207 (x0 : real) := and ((fun y0 : real => (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) x0).
Definition term339 := (~ ((forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)))) \/ (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1))).
Definition term471 (x0 : real) (x1 : real) := ((x1 = x0) /\ (real_le x0 x1)) -> False.
Definition term447 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = x0)) \/ (~ (real_le x1 y0))) /\ ((~ (y0 = x1)) \/ (~ (real_le x1 y0))).
Definition term444 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = x1)) \/ (~ (real_le x1 y0))) /\ ((~ (y0 = x0)) \/ (~ (real_le x1 y0))).
Definition term315 (x0 : real) (x1 : real) (x2 : real) := ((x1 = x0) \/ (x1 = x2)) /\ (~ ((real_le x1 x0) \/ (real_le x1 x2))).
Definition term54 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le (sup x0) x1) = (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term421 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term118 (x0 : real) (x1 : real) := (x1 = x0) \/ (@IN real x1 (@EMPTY real)).
Definition term46 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le y0 (sup x0)) = (exists y1 : real, (@IN real y1 x0) /\ (real_le y0 y1))) x1.
Definition term117 (x0 : real) (x1 : real) := @IN real x0 (@INSERT real x1 (@EMPTY real)).
Definition term333 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)) x0).
Definition term304 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)) x0).
Definition term282 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) x0).
Definition term437 (x0 : real) := fun y0 : real => exists y1 : real, ((forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y0))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y0))) \/ (~ (real_le y0 y2)))) \/ (((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0)))).
Definition term329 (x0 : real) := fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0))).
Definition term263 (x0 : real -> Prop) := ~ (ex x0).
Definition term61 (x0 : real) (x1 : real) := real_le (real_max x0 x1) (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))).
Definition term196 (x0 : real) := forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1).
Definition term191 (x0 : real) := forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1).
Definition term55 (x0 : real -> Prop) (x1 : real) := real_le (sup x0) x1.
Definition term286 (x0 : real) (x1 : real) (x2 : real) := (~ ((x2 = x0) \/ (x2 = x1))) \/ (~ (real_le x1 x2)).
Definition term260 (x0 : real) (x1 : real) (x2 : real) := (~ ((x2 = x1) \/ (x2 = x0))) \/ (~ (real_le x1 x2)).
Definition term254 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term15 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term416 (x0 : real) (x1 : real) := ((fun y0 : real => (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))) x1) \/ ((fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0)))) x1).
Definition term34 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, ~ ((@INSERT a0 x0 y0) = (@EMPTY a0)).
Definition term244 := ~ (((forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1))).
Definition term273 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term156 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term321 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((y0 = x0) \/ (y0 = x1)) -> (real_le y0 x0) \/ (real_le y0 x1)) x2).
Definition term292 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ (real_le x1 y0)) x2).
Definition term268 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((y0 = x1) \/ (y0 = x0)) /\ (real_le x1 y0)) x2).
Definition term448 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term57 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0))) x0.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((@INSERT a0 x0 x1) = (@EMPTY a0)).
Definition term221 := (forall y0 : real, (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term177 (x0 : real) := (forall y0 : real, (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))) /\ (forall y0 : real, forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0)).
Definition term423 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term43 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @FINITE a0 (@INSERT a0 x0 x1).
Definition term204 := fun y0 : real => (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)).
Definition term148 := (~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> False.
Definition term214 := forall y0 : real, (fun y1 : real => (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) /\ (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3))) y0.
Definition term170 (x0 : real) := forall y0 : real, (fun y1 : real => (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) /\ (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2))) y0.
Definition term119 (x0 : real) (x1 : real) := or (x0 = x1).
Definition term252 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term93 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) := forall y0 : Prop, ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) = x3) -> (x3 -> (real_le x0 (real_max x1 x2)) = y0) -> ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> real_le x0 (real_max x1 x2)) = (x3 -> y0).
Definition term88 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term136 (x0 : real) (x1 : real) := and ((exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (real_le x0 y0)) /\ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (real_le x1 y0))).
Definition term83 (x0 : real) (x1 : real) := and ((exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x0 y0)) /\ (exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x1 y0))).
Definition term230 := fun y0 : real => ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0) /\ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3)) y0).
Definition term210 := fun y0 : real => ((fun y1 : real => (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) /\ (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> (real_le y3 y1) \/ (real_le y3 y2)) y0).
Definition term186 (x0 : real) := fun y0 : real => ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0) /\ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2)) y0).
Definition term166 (x0 : real) := fun y0 : real => ((fun y1 : real => (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) /\ (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> (real_le y2 x0) \/ (real_le y2 y1)) y0).
Definition term464 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0)) x1.
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0))) x2.
Definition term145 := fun y0 : real => forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term111 := fun y0 : real => forall y1 : real, ((exists y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) /\ (real_le y0 y2)) /\ (exists y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) /\ (real_le y1 y2))) /\ (forall y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term132 (x0 : real) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le x1 y0).
Definition term126 (x0 : real) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) /\ (real_le x1 y0).
Definition term86 (x0 : real) (x1 : real) := forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le y0 (real_max x0 x1).
Definition term11 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term316 (x0 : real) (x1 : real) (x2 : real) := ((x1 = x0) \/ (x1 = x2)) /\ ((~ (real_le x1 x0)) /\ (~ (real_le x1 x2))).
Definition term90 (x0 : real) (x1 : real) (x2 : real) := forall y0 : Prop, forall y1 : Prop, ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) = y0) -> (y0 -> (real_le x0 (real_max x1 x2)) = y1) -> ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> real_le x0 (real_max x1 x2)) = (y0 -> y1).
Definition term89 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term312 := ~ ((forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))).
Definition term183 (x0 : real) (x1 : real) := and ((fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) x1).
Definition term369 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1))) x1.
Definition term365 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) x1.
Definition term164 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0)) x1.
Definition term28 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le (real_max x0 y0) y1) = ((real_le x0 y1) /\ (real_le y0 y1))) x1.
Definition term21 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le y1 (real_max x0 y0)) = ((real_le y1 x0) \/ (real_le y1 y0))) x1.
Definition term122 (x0 : real) (x1 : real) (x2 : real) := and (@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))).
Definition term106 (x0 : real) := fun y0 : real => (real_max x0 y0) = (sup (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))).
Definition term337 := or (~ ((forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)))).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((@INSERT a0 x0 x1) = (@EMPTY a0))) -> ((@INSERT a0 x0 x1) = (@EMPTY a0)) = False.
Definition term71 (x0 : real) (x1 : real) := and (@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))).
Definition term94 (x0 : real) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) = x3) -> (x3 -> (real_le x0 (real_max x1 x2)) = y0) -> ((@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> real_le x0 (real_max x1 x2)) = (x3 -> y0)) x4.
Definition term462 (x0 : real) := (real_le x0 x0) -> ~ (real_le x0 x0).
Definition term160 (x0 : real) := fun y0 : real => (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1)).
Definition term404 (x0 : real) := exists y0 : real, ((fun y1 : real => (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) y0) \/ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((~ (real_le y2 x0)) /\ (~ (real_le y2 y1)))) y0).
Definition term386 := exists y0 : real, ((fun y1 : real => exists y2 : real, (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) \/ (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3)))) y0) \/ ((fun y1 : real => exists y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((~ (real_le y3 y1)) /\ (~ (real_le y3 y2)))) y0).
Definition term364 (x0 : real) := exists y0 : real, ((fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) y0) \/ ((fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))) y0).
Definition term346 := exists y0 : real, ((fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) y0) \/ ((fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3))) y0).
Definition term401 := fun y0 : real => (exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) \/ (exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1)))).
Definition term361 := fun y0 : real => (exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))).
Definition term424 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term259 (x0 : real) (x1 : real) (x2 : real) := or ((~ (x1 = x0)) /\ (~ (x1 = x2))).
Definition term100 (x0 : real) (x1 : real) (x2 : real) := (@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) -> real_le x0 (real_max x1 x2).
Definition term66 (x0 : real) (x1 : real -> Prop) := (@FINITE real x1) -> (@FINITE real (@INSERT real x0 x1)) = True.
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@FINITE a0 (@INSERT a0 x0 x1)) = True.
Definition term473 (x0 : real) := (x0 = x0) /\ (real_le x0 x0).
Definition term206 (x0 : real) := (fun y0 : real => (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) x0.
Definition term181 (x0 : real) := fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1).
Definition term180 (x0 : real) := fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1).
Definition term255 (x0 : real) (x1 : real) (x2 : real) := ~ ((x1 = x0) \/ (x1 = x2)).
Definition term205 := fun y0 : real => forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1).
Definition term327 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0)) x1).
Definition term298 (x0 : real) (x1 : real) := ~ ((fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1)) x1).
Definition term276 (x0 : real) (x1 : real) := ~ ((fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) x1).
Definition term439 := fun y0 : real => exists y1 : real, exists y2 : real, ((forall y3 : real, ((~ (y3 = y0)) /\ (~ (y3 = y1))) \/ (~ (real_le y0 y3))) \/ (forall y3 : real, ((~ (y3 = y0)) /\ (~ (y3 = y1))) \/ (~ (real_le y1 y3)))) \/ (((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1)))).
Definition term335 := fun y0 : real => exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1))).
Definition term455 (x0 : real) := (fun y0 : real => ~ (real_le y0 x0)) x0.
Definition term53 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le (sup x0) y0) = (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) x1.
Definition term171 (x0 : real) := forall y0 : real, (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1)).
Definition term114 (x0 : real) (x1 : real) (x2 : real -> Prop) := @IN real x0 (@INSERT real x1 x2).
Definition term257 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term414 (x0 : real) (x1 : real) := or ((fun y0 : real => (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))) x1).
Definition term39 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1)) x0.
Definition term125 (x0 : real) (x1 : real) (x2 : real) := ((x2 = x1) \/ (x2 = x0)) /\ (real_le x1 x2).
Definition term215 := forall y0 : real, (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)).
Definition term25 (x0 : real) (x1 : real) (x2 : real) := (real_le x1 x0) \/ (real_le x1 x2).
Definition term116 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) \/ (@IN real x1 (@INSERT real x2 (@EMPTY real))).
Definition term474 (x0 : real) := ((x0 = x0) /\ (real_le x0 x0)) -> False.
Definition term457 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => ~ (real_le y0 x0)) x1).
Definition term428 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 x1)))) y0.
Definition term48 (x0 : real -> Prop) := (@FINITE real x0) /\ (~ (x0 = (@EMPTY real))).
Definition term239 := forall y0 : real, (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3)) y0.
Definition term234 := forall y0 : real, (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0.
Definition term219 := forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> (real_le y3 y1) \/ (real_le y3 y2)) y0.
Definition term195 (x0 : real) := forall y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2)) y0.
Definition term190 (x0 : real) := forall y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0.
Definition term175 (x0 : real) := forall y0 : real, (fun y1 : real => forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> (real_le y2 x0) \/ (real_le y2 y1)) y0.
Definition term30 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le (real_max x0 x1) y0) = ((real_le x0 y0) /\ (real_le x1 y0))) x2.
Definition term324 (x0 : real) (x1 : real) := exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ ((~ (real_le y0 x0)) /\ (~ (real_le y0 x1))).
Definition term165 (x0 : real) (x1 : real) := ((fun y0 : real => (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))) x1) /\ ((fun y0 : real => forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0)) x1).
Definition term391 (x0 : real) := (fun y0 : real => exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1)))) x0.
Definition term351 (x0 : real) := (fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))) x0.
Definition term347 (x0 : real) := (fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) x0.
Definition term229 (x0 : real) := ((fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) x0) /\ ((fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)) x0).
Definition term460 (x0 : real) := ~ (x0 = x0).
Definition term73 (x0 : real) (x1 : real) := (@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (~ ((@INSERT real x0 (@INSERT real x1 (@EMPTY real))) = (@EMPTY real))).
Definition term415 (x0 : real) (x1 : real) := or ((forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x0 y0))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0)))).
Definition term310 := (~ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2))) \/ (~ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))).
Definition term290 (x0 : real) (x1 : real) := forall y0 : real, ~ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ (real_le x1 y1)) y0).
Definition term266 (x0 : real) (x1 : real) := forall y0 : real, ~ ((fun y1 : real => ((y1 = x1) \/ (y1 = x0)) /\ (real_le x1 y1)) y0).
Definition term425 (x0 : real) (x1 : real) := ((forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x0 y0))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0)))) \/ (exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 x1)))) y0).
Definition term250 := (~ (((forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term322 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) -> (real_le y1 x0) \/ (real_le y1 x1)) y0).
Definition term293 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ (real_le x1 y1)) y0).
Definition term269 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((y1 = x1) \/ (y1 = x0)) /\ (real_le x1 y1)) y0).
Definition term445 (x0 : real) (x1 : real) (x2 : real) := ((~ (x2 = x0)) \/ (~ (real_le x1 x2))) /\ ((~ (x2 = x1)) \/ (~ (real_le x1 x2))).
Definition term441 (x0 : real) (x1 : real) (x2 : real) := ((~ (x2 = x1)) \/ (~ (real_le x1 x2))) /\ ((~ (x2 = x0)) \/ (~ (real_le x1 x2))).
Definition term70 (x0 : real) (x1 : real) := @FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real))).
Definition term436 (x0 : real) (x1 : real) := exists y0 : real, ((forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ (~ (real_le x1 y1)))) \/ (((y0 = x0) \/ (y0 = x1)) /\ ((~ (real_le y0 x0)) /\ (~ (real_le y0 x1)))).
Definition term157 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term2 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term209 (x0 : real) := ((fun y0 : real => (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) x0) /\ ((fun y0 : real => forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)) x0).
Definition term64 (x0 : real) (x1 : real) := @INSERT real x0 (@INSERT real x1 (@EMPTY real)).
Definition term24 (x0 : real) (x1 : real) (x2 : real) := real_le x0 (real_max x1 x2).
Definition term246 := imp (~ (((forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))).
Definition term29 (x0 : real) (x1 : real) := forall y0 : real, (real_le (real_max x0 x1) y0) = ((real_le x0 y0) /\ (real_le x1 y0)).
Definition term14 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term454 (x0 : real) (x1 : real) := (fun y0 : real => ~ (real_le y0 x0)) x1.
Definition term23 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le y0 (real_max x0 x1)) = ((real_le y0 x0) \/ (real_le y0 x1))) x2.
Definition term151 := ((~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term76 (x0 : real) (x1 : real) := and (real_le x0 (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))).
Definition term243 := ((forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)).
Definition term199 (x0 : real) := ((forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))) /\ (forall y0 : real, forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> (real_le y1 x0) \/ (real_le y1 y0)).
Definition term153 := (((~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> ((~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term140 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x0) \/ (y0 = x1)) -> (real_le y0 x0) \/ (real_le y0 x1).
Definition term163 (x0 : real) (x1 : real) := and ((fun y0 : real => (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le x0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (real_le y0 y1))) x1).
Definition term402 := exists y0 : real, (exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) \/ (exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1)))).
Definition term362 := exists y0 : real, (exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))).
Definition term418 (x0 : real) := fun y0 : real => ((fun y1 : real => (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) y0) \/ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((~ (real_le y2 x0)) /\ (~ (real_le y2 y1)))) y0).
Definition term400 := fun y0 : real => ((fun y1 : real => exists y2 : real, (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) \/ (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3)))) y0) \/ ((fun y1 : real => exists y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((~ (real_le y3 y1)) /\ (~ (real_le y3 y2)))) y0).
Definition term378 (x0 : real) := fun y0 : real => ((fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) y0) \/ ((fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))) y0).
Definition term360 := fun y0 : real => ((fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) y0) \/ ((fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3))) y0).
Definition term476 (x0 : real) := (real_le x0 x0) -> False.
Definition term397 (x0 : real) := or (exists y0 : real, (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))).
Definition term38 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1).
Definition term4 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term317 (x0 : real) (x1 : real) (x2 : real) := ~ (((x1 = x0) \/ (x1 = x2)) -> (real_le x1 x0) \/ (real_le x1 x2)).
Definition term228 (x0 : real) := (fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2)) x0.
Definition term226 (x0 : real) := (fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) x0.
Definition term208 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)) x0.
Definition term26 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le (real_max y0 y1) y2) = ((real_le y0 y2) /\ (real_le y1 y2))) x0.
Definition term19 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le y2 (real_max y0 y1)) = ((real_le y2 y0) \/ (real_le y2 y1))) x0.
Definition term383 := or (exists y0 : real, exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))).
Definition term357 (x0 : real) := or (exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))).
Definition term309 := or (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))).
Definition term342 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term129 (x0 : real) (x1 : real) := and (exists y0 : real, ((y0 = x1) \/ (y0 = x0)) /\ (real_le x1 y0)).
Definition term77 (x0 : real) (x1 : real) := and (exists y0 : real, (@IN real y0 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) /\ (real_le x1 y0)).
Definition term62 (x0 : real) (x1 : real) := (real_le x0 (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))) /\ (real_le x1 (sup (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))).
Definition term295 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ (~ (real_le x1 y0)).
Definition term271 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = x1)) /\ (~ (y0 = x0))) \/ (~ (real_le x1 y0)).
Definition term222 := forall y0 : real, ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) y0) /\ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3)) y0).
Definition term202 := forall y0 : real, ((fun y1 : real => (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y1 y3)) /\ (forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ (real_le y2 y3))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> (real_le y3 y1) \/ (real_le y3 y2)) y0).
Definition term178 (x0 : real) := forall y0 : real, ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) y0) /\ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2)) y0).
Definition term158 (x0 : real) := forall y0 : real, ((fun y1 : real => (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le x0 y2)) /\ (exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ (real_le y1 y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> (real_le y2 x0) \/ (real_le y2 y1)) y0).
Definition term466 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term403 (x0 : real) := (exists y0 : real, (fun y1 : real => (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((~ (real_le y2 x0)) /\ (~ (real_le y2 y1)))) y0).
Definition term385 := (exists y0 : real, (fun y1 : real => exists y2 : real, (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) \/ (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((~ (real_le y3 y1)) /\ (~ (real_le y3 y2)))) y0).
Definition term363 (x0 : real) := (exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) y0) \/ (exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))) y0).
Definition term345 := (exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3))) y0).
Definition term449 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term101 (x0 : real) (x1 : real) (x2 : real) := (@IN real x1 (@INSERT real x0 (@INSERT real x2 (@EMPTY real)))) -> (real_le x1 x0) \/ (real_le x1 x2).
Definition term245 := imp (~ (forall y0 : real, forall y1 : real, ((exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y0 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (real_le y1 y2))) /\ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> (real_le y2 y0) \/ (real_le y2 y1)))).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term463 (x0 : Prop) := x0 -> ~ x0.
Definition term300 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)).
Definition term278 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1)).
Definition term110 := fun y0 : real => forall y1 : real, (real_max y0 y1) = (sup (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term374 (x0 : real) (x1 : real) := or ((fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) x1).
Definition term289 (x0 : real) (x1 : real) := ~ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (real_le x1 y0)).
Definition term265 (x0 : real) (x1 : real) := ~ (exists y0 : real, ((y0 = x1) \/ (y0 = x0)) /\ (real_le x1 y0)).
Definition term411 (x0 : real) := exists y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((~ (real_le y2 x0)) /\ (~ (real_le y2 y1)))) y0.
Definition term393 := exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((~ (real_le y3 y1)) /\ (~ (real_le y3 y2)))) y0.
Definition term389 := exists y0 : real, (fun y1 : real => exists y2 : real, (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) \/ (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3)))) y0.
Definition term371 (x0 : real) := exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))) y0.
Definition term367 (x0 : real) := exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) y0.
Definition term353 := exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3))) y0.
Definition term349 := exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) y0.
Definition term413 (x0 : real) := @eq Prop ((exists y0 : real, (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))) \/ (exists y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((~ (real_le y1 x0)) /\ (~ (real_le y1 y0))))).
Definition term412 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((~ (real_le y2 x0)) /\ (~ (real_le y2 y1)))) y0)).
Definition term395 := @eq Prop ((exists y0 : real, exists y1 : real, (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))) \/ (exists y0 : real, exists y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((~ (real_le y2 y0)) /\ (~ (real_le y2 y1))))).
Definition term394 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) \/ (forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((~ (real_le y3 y1)) /\ (~ (real_le y3 y2)))) y0)).
Definition term373 (x0 : real) := @eq Prop ((exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le x0 y1))) \/ (exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ (~ (real_le y0 y1)))).
Definition term372 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le x0 y2))) y0) \/ (exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2))) y0)).
Definition term355 := @eq Prop ((exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y0 y2))) \/ (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ (~ (real_le y1 y2)))).
Definition term354 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y1 y3))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ (~ (real_le y2 y3))) y0)).
