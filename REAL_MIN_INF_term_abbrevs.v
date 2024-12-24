Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term440 (x0 : real) (x1 : real) := imp ((x0 = x1) /\ (real_le x0 x1)).
Definition term13 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term1 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term294 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ ((fun y1 : real => ((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1))) y0).
Definition term12 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term33 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, ~ ((@INSERT a0 y0 y1) = (@EMPTY a0))) x0.
Definition term274 (x0 : real) (x1 : real) := (exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) y0) /\ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x1 y0))).
Definition term419 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term201 (x0 : real -> Prop) := ~ (all x0).
Definition term417 := (~ False) -> False.
Definition term138 := (~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term408 (x0 : real) (x1 : real) := @eq Prop (~ (real_le x0 x1)).
Definition term451 (x0 : real) (x1 : real) := (x1 = x1) /\ ((real_le x1 x0) /\ (real_le x1 x1)).
Definition term387 (x0 : real) (x1 : real) := fun y0 : real => exists y1 : real, ((((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = x1))) \/ ((~ (real_le y2 x0)) \/ (~ (real_le y2 x1)))).
Definition term234 := fun y0 : real => exists y1 : real, (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y1 y2))).
Definition term237 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) /\ (~ (x1 = x2)).
Definition term337 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) x1.
Definition term286 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) y0) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1))).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1))) x1.
Definition term91 (x0 : real) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ ((real_le y0 x0) /\ (real_le y0 x1)).
Definition term331 (x0 : real) := (exists y0 : real, exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) \/ (exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 y0)))).
Definition term312 := (exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) \/ (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1)))).
Definition term269 := (exists y0 : real, exists y1 : real, (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y1 y2)))) \/ (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1)))).
Definition term296 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1))) y0.
Definition term277 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ((y1 = x1) \/ (y1 = x0)) /\ (~ (real_le x1 y1))) y0.
Definition term82 (x0 : real) (x1 : real) := and (real_le (real_min x0 x1) (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))).
Definition term433 (x0 : Prop) := ~ (~ x0).
Definition term399 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (y0 = x0)) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1)))) /\ ((~ (y0 = x1)) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1))))) x2.
Definition term23 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le y0 (real_min x0 x1)) = ((real_le y0 x0) /\ (real_le y0 x1))) x2.
Definition term183 := and (forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)).
Definition term370 (x0 : real) (x1 : real) := fun y0 : real => (exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 x1)))).
Definition term351 (x0 : real) := fun y0 : real => (exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 y0)))).
Definition term111 (x0 : real) (x1 : real) (x2 : real) := imp (@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))).
Definition term373 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, ((fun y1 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1)))) y0) \/ (forall y1 : real, ((~ (y1 = x1)) /\ (~ (y1 = x2))) \/ ((~ (real_le y1 x1)) \/ (~ (real_le y1 x2)))).
Definition term358 (x0 : real) (x1 : real) := exists y0 : real, ((fun y1 : real => exists y2 : real, (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = x1)) /\ (~ (real_le x1 y2)))) y0) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 x1)))).
Definition term109 (x0 : real) (x1 : real) := (x0 = x1) \/ False.
Definition term72 (x0 : real) (x1 : real) := ~ ((@INSERT real x0 (@INSERT real x1 (@EMPTY real))) = (@EMPTY real)).
Definition term291 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term161 (x0 : real) := and (forall y0 : real, (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)).
Definition term24 (x0 : real) (x1 : real) (x2 : real) := real_le x0 (real_min x1 x2).
Definition term119 (x0 : real) (x1 : real) (x2 : real) := (@IN real x2 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x1 x2.
Definition term113 (x0 : real) (x1 : real) (x2 : real) := (@IN real x2 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) -> real_le x1 x2.
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term239 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ (~ (real_le x1 x2)).
Definition term437 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term190 := imp (~ ((forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))).
Definition term173 (x0 : real) := and ((fun y0 : real => forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) x0).
Definition term313 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term197 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term152 (x0 : real) (x1 : real) := (fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0))) x1.
Definition term221 (x0 : real) (x1 : real) := (~ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x0 y0)) /\ (~ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0)).
Definition term208 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x1) \/ (y0 = x0)) /\ (~ (real_le x1 y0)).
Definition term89 (x0 : real) (x1 : real) (x2 : real) := (@IN real x1 (@INSERT real x0 (@INSERT real x2 (@EMPTY real)))) /\ ((real_le x1 x0) /\ (real_le x1 x2)).
Definition term259 (x0 : real) := exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 y0))).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term182 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0).
Definition term160 (x0 : real) := and (forall y0 : real, (fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0).
Definition term264 := fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1))).
Definition term290 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term135 (x0 : Prop) := (~ x0) -> False.
Definition term353 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term439 (x0 : real) (x1 : real) := imp (~ ((~ (x0 = x1)) \/ (~ (real_le x0 x1)))).
Definition term56 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (real_le y0 x1).
Definition term224 (x0 : real) := ~ (forall y0 : real, (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)).
Definition term212 (x0 : real) (x1 : real) := ~ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0).
Definition term203 (x0 : real) (x1 : real) := ~ (forall y0 : real, ((y0 = x1) \/ (y0 = x0)) -> real_le x1 y0).
Definition term441 (x0 : real) (x1 : real) (x2 : real) := ((x1 = x0) /\ (real_le x1 x0)) -> ~ (real_le x1 x2).
Definition term104 (x0 : real) (x1 : real) (x2 : real) := @IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real))).
Definition term86 (x0 : real) (x1 : real) := exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le y0 (real_min x0 x1)).
Definition term76 (x0 : real) (x1 : real) := or (real_le x0 (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))).
Definition term386 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, ((((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0)))) \/ (forall y1 : real, ((~ (y1 = x1)) /\ (~ (y1 = x2))) \/ ((~ (real_le y1 x1)) \/ (~ (real_le y1 x2)))).
Definition term328 (x0 : real) := or ((fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) x0).
Definition term273 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term74 (x0 : real) (x1 : real) := real_le x0 (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))).
Definition term195 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term253 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1))).
Definition term187 := (forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))).
Definition term148 (x0 : real) := fun y0 : real => (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1).
Definition term157 (x0 : real) := fun y0 : real => (fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0.
Definition term226 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)) x1).
Definition term58 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0))) x1.
Definition term96 (x0 : real) := forall y0 : real, (real_min x0 y0) = (inf (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))).
Definition term53 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le (inf x0) y0) = (exists y1 : real, (@IN real y1 x0) /\ (real_le y1 y0))) x1.
Definition term412 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term30 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le (real_min x0 x1) y0) = ((real_le x0 y0) \/ (real_le x1 y0))) x2.
Definition term110 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) \/ (x1 = x2).
Definition term169 := (forall y0 : real, (fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((real_le y3 y1) /\ (real_le y3 y2))) y0).
Definition term147 (x0 : real) := (forall y0 : real, (fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0) /\ (forall y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((real_le y2 x0) /\ (real_le y2 y1))) y0).
Definition term348 (x0 : real) (x1 : real) := ((fun y0 : real => exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) x1) \/ ((fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 y0)))) x1).
Definition term3 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2))) x0.
Definition term355 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) \/ x1.
Definition term289 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term421 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term444 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term415 (x0 : Prop) := (~ x0) -> x0.
Definition term301 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((x3 = x1) \/ (x3 = x2)) /\ (~ (real_le x2 x3))).
Definition term404 (x0 : real) (x1 : real) := (fun y0 : real => ~ (real_le x0 y0)) x1.
Definition term285 (x0 : real) (x1 : real) (x2 : real) := (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (exists y0 : real, ((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0))).
Definition term342 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 x0)) \/ (~ (real_le y2 y1)))) y0.
Definition term184 := fun y0 : real => (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((real_le y3 y1) /\ (real_le y3 y2))) y0.
Definition term179 := fun y0 : real => (fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0.
Definition term295 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x1 y0))) x2.
Definition term276 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x1) \/ (y0 = x0)) /\ (~ (real_le x1 y0))) x2.
Definition term171 := fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1)).
Definition term59 (x0 : real) (x1 : real) := inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real))).
Definition term112 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) \/ (x1 = x2)).
Definition term430 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term85 (x0 : real) (x1 : real) := real_le (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) (real_min x0 x1).
Definition term447 (x0 : real) (x1 : real) (x2 : real) := ~ ((x1 = x2) /\ ((real_le x1 x0) /\ (real_le x1 x2))).
Definition term40 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0).
Definition term376 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, (fun y1 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1)))) y0.
Definition term297 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1))) y0.
Definition term278 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => ((y1 = x1) \/ (y1 = x0)) /\ (~ (real_le x1 y1))) y0.
Definition term150 (x0 : real) (x1 : real) := (fun y0 : real => (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)) x1.
Definition term445 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term193 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term186 := forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1)).
Definition term181 := forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2).
Definition term134 := forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))).
Definition term101 := forall y0 : real, forall y1 : real, ((forall y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) -> real_le y0 y2) \/ (forall y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) -> real_le y1 y2)) /\ (exists y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) /\ ((real_le y2 y0) /\ (real_le y2 y1))).
Definition term100 := forall y0 : real, forall y1 : real, (real_min y0 y1) = (inf (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))).
Definition term27 (x0 : real) := forall y0 : real, forall y1 : real, (real_le (real_min x0 y0) y1) = ((real_le x0 y1) \/ (real_le y0 y1)).
Definition term20 (x0 : real) := forall y0 : real, forall y1 : real, (real_le y1 (real_min x0 y0)) = ((real_le y1 x0) /\ (real_le y1 y0)).
Definition term18 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term17 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term266 := or (~ (forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2))).
Definition term78 (x0 : real) (x1 : real) := ((@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (~ ((@INSERT real x0 (@INSERT real x1 (@EMPTY real))) = (@EMPTY real)))) -> (real_le x1 (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))) = (forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x1 y0).
Definition term63 (x0 : real) (x1 : real) := ((@FINITE real (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) /\ (~ ((@INSERT real x1 (@INSERT real x0 (@EMPTY real))) = (@EMPTY real)))) -> (real_le x1 (inf (@INSERT real x1 (@INSERT real x0 (@EMPTY real))))) = (forall y0 : real, (@IN real y0 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) -> real_le x1 y0).
Definition term392 := exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, ((((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) \/ (forall y4 : real, ((~ (y4 = y0)) /\ (~ (y4 = y1))) \/ ((~ (real_le y4 y0)) \/ (~ (real_le y4 y1)))).
Definition term390 (x0 : real) := exists y0 : real, exists y1 : real, exists y2 : real, ((((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) \/ (forall y3 : real, ((~ (y3 = x0)) /\ (~ (y3 = y0))) \/ ((~ (real_le y3 x0)) \/ (~ (real_le y3 y0)))).
Definition term388 (x0 : real) (x1 : real) := exists y0 : real, exists y1 : real, ((((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))) \/ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = x1))) \/ ((~ (real_le y2 x0)) \/ (~ (real_le y2 x1)))).
Definition term310 := exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3))).
Definition term308 (x0 : real) := exists y0 : real, exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2))).
Definition term306 (x0 : real) (x1 : real) := exists y0 : real, exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1))).
Definition term265 := exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1))).
Definition term235 := exists y0 : real, exists y1 : real, (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y1 y2))).
Definition term246 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term118 (x0 : real) (x1 : real) := or (forall y0 : real, ((y0 = x1) \/ (y0 = x0)) -> real_le x1 y0).
Definition term77 (x0 : real) (x1 : real) := or (forall y0 : real, (@IN real y0 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) -> real_le x1 y0).
Definition term292 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term377 (x0 : real) (x1 : real) (x2 : real) := or (exists y0 : real, (fun y1 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1)))) y0).
Definition term362 (x0 : real) (x1 : real) := or (exists y0 : real, (fun y1 : real => exists y2 : real, (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = x1)) /\ (~ (real_le x1 y2)))) y0).
Definition term340 (x0 : real) := or (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, (((y2 = x0) \/ (y2 = y1)) /\ (~ (real_le x0 y2))) /\ (((y3 = x0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) y0).
Definition term322 := or (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, exists y4 : real, (((y3 = y1) \/ (y3 = y2)) /\ (~ (real_le y1 y3))) /\ (((y4 = y1) \/ (y4 = y2)) /\ (~ (real_le y2 y4)))) y0).
Definition term283 (x0 : real) (x1 : real) (x2 : real) := and (((x2 = x1) \/ (x2 = x0)) /\ (~ (real_le x1 x2))).
Definition term423 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> @FINITE a0 (@INSERT a0 x0 x1).
Definition term52 (x0 : real -> Prop) := forall y0 : real, ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le (inf x0) y0) = (exists y1 : real, (@IN real y1 x0) /\ (real_le y1 y0)).
Definition term45 (x0 : real -> Prop) := forall y0 : real, ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le y0 (inf x0)) = (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term406 (x0 : real) := ~ (real_le x0 x0).
Definition term372 (x0 : real) (x1 : real) (x2 : real) := (exists y0 : real, (fun y1 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1)))) y0) \/ (forall y0 : real, ((~ (y0 = x1)) /\ (~ (y0 = x2))) \/ ((~ (real_le y0 x1)) \/ (~ (real_le y0 x2)))).
Definition term357 (x0 : real) (x1 : real) := (exists y0 : real, (fun y1 : real => exists y2 : real, (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = x1)) /\ (~ (real_le x1 y2)))) y0) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1)))).
Definition term261 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((real_le y3 y1) /\ (real_le y3 y2))) y0).
Definition term255 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((real_le y2 x0) /\ (real_le y2 y1))) y0).
Definition term231 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0).
Definition term225 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0).
Definition term213 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) -> real_le x1 y1) y0).
Definition term204 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((y1 = x1) \/ (y1 = x0)) -> real_le x1 y1) y0).
Definition term367 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => exists y1 : real, (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x1 y0))) /\ (((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1)))) x0) \/ (forall y0 : real, ((~ (y0 = x1)) /\ (~ (y0 = x2))) \/ ((~ (real_le y0 x1)) \/ (~ (real_le y0 x2)))).
Definition term243 (x0 : real) (x1 : real) (x2 : real) := ((~ (x1 = x0)) /\ (~ (x1 = x2))) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x1 x2))).
Definition term222 (x0 : real) (x1 : real) := (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x1 y0))).
Definition term51 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (real_le (inf y0) y1) = (exists y2 : real, (@IN real y2 y0) /\ (real_le y2 y1))) x0.
Definition term44 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (real_le y1 (inf y0)) = (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) x0.
Definition term238 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x1 x0) /\ (real_le x1 x2)).
Definition term22 (x0 : real) (x1 : real) := forall y0 : real, (real_le y0 (real_min x0 x1)) = ((real_le y0 x0) /\ (real_le y0 x1)).
Definition term124 (x0 : real) (x1 : real) := (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x0 y0) \/ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0).
Definition term81 (x0 : real) (x1 : real) := (forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x0 y0) \/ (forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x1 y0).
Definition term263 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((real_le y3 y1) /\ (real_le y3 y2))) y0).
Definition term257 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((real_le y2 x0) /\ (real_le y2 y1))) y0).
Definition term233 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0).
Definition term178 := @eq Prop (forall y0 : real, (forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1)))).
Definition term177 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0) /\ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((real_le y3 y1) /\ (real_le y3 y2))) y0)).
Definition term156 (x0 : real) := @eq Prop (forall y0 : real, ((forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0)))).
Definition term155 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0) /\ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((real_le y2 x0) /\ (real_le y2 y1))) y0)).
Definition term68 (x0 : real) := (@FINITE real (@EMPTY real)) -> (@FINITE real (@INSERT real x0 (@EMPTY real))) = True.
Definition term126 (x0 : real) (x1 : real) (x2 : real) := and ((x1 = x0) \/ (x1 = x2)).
Definition term452 (x0 : real) (x1 : real) := ((x1 = x1) /\ ((real_le x1 x0) /\ (real_le x1 x1))) -> False.
Definition term448 (x0 : real) (x1 : real) (x2 : real) := ((x1 = x2) /\ ((real_le x1 x0) /\ (real_le x1 x2))) -> False.
Definition term446 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x2)) \/ (~ ((real_le x1 x0) /\ (real_le x1 x2))).
Definition term303 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0))).
Definition term258 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 y0))).
Definition term16 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term379 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((exists y0 : real, (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0)))) \/ (forall y0 : real, ((~ (y0 = x1)) /\ (~ (y0 = x2))) \/ ((~ (real_le y0 x1)) \/ (~ (real_le y0 x2))))).
Definition term378 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1)))) y0) \/ (forall y0 : real, ((~ (y0 = x1)) /\ (~ (y0 = x2))) \/ ((~ (real_le y0 x1)) \/ (~ (real_le y0 x2))))).
Definition term364 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1))))).
Definition term363 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = x1)) /\ (~ (real_le x1 y2)))) y0) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1))))).
Definition term414 (x0 : real) := (~ (real_le x0 x0)) -> real_le x0 x0.
Definition term281 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x1 y0)))).
Definition term280 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) y0) /\ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x1 y0)))).
Definition term293 (x0 : real) (x1 : real) (x2 : real) := (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (exists y0 : real, (fun y1 : real => ((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1))) y0).
Definition term191 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ~ ((@INSERT a0 x0 y0) = (@EMPTY a0))) x1.
Definition term330 (x0 : real) := ((fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) x0) \/ ((fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1)))) x0).
Definition term10 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term69 (x0 : real) := @FINITE real (@INSERT real x0 (@EMPTY real)).
Definition term200 (x0 : real) (x1 : real) (x2 : real) := ((x2 = x1) \/ (x2 = x0)) /\ (~ (real_le x1 x2)).
Definition term394 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term159 (x0 : real) := forall y0 : real, (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1).
Definition term316 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term260 := ~ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))).
Definition term254 (x0 : real) := ~ (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0))).
Definition term230 := ~ (forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)).
Definition term192 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term137 := ~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1)))).
Definition term242 (x0 : real) (x1 : real) (x2 : real) := (~ ((x1 = x0) \/ (x1 = x2))) \/ (~ ((real_le x1 x0) /\ (real_le x1 x2))).
Definition term103 (x0 : real) (x1 : real) (x2 : real -> Prop) := (x1 = x0) \/ (@IN real x1 x2).
Definition term356 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) \/ x1.
Definition term140 := (((~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term130 (x0 : real) (x1 : real) := ((forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x0 y0) \/ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0)) /\ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ ((real_le y0 x0) /\ (real_le y0 x1))).
Definition term93 (x0 : real) (x1 : real) := ((forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x0 y0) \/ (forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x1 y0)) /\ (exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ ((real_le y0 x0) /\ (real_le y0 x1))).
Definition term127 (x0 : real) (x1 : real) (x2 : real) := ((x1 = x0) \/ (x1 = x2)) /\ ((real_le x1 x0) /\ (real_le x1 x2)).
Definition term47 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le x1 (inf x0)) = (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term67 (x0 : real) (x1 : real) := (@FINITE real (@INSERT real x1 (@EMPTY real))) -> (@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) = True.
Definition term218 (x0 : real) (x1 : real) := exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x1 y0)).
Definition term209 (x0 : real) (x1 : real) := exists y0 : real, ((y0 = x1) \/ (y0 = x0)) /\ (~ (real_le x1 y0)).
Definition term450 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x1 x1).
Definition term418 (x0 : real) (x1 : real) := (real_le x0 x1) -> ~ (real_le x0 x1).
Definition term360 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = x1)) /\ (~ (real_le x1 y2)))) y0.
Definition term338 (x0 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, exists y3 : real, (((y2 = x0) \/ (y2 = y1)) /\ (~ (real_le x0 y2))) /\ (((y3 = x0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) y0.
Definition term324 := fun y0 : real => (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ ((~ (real_le y3 y1)) \/ (~ (real_le y3 y2)))) y0.
Definition term320 := fun y0 : real => (fun y1 : real => exists y2 : real, exists y3 : real, exists y4 : real, (((y3 = y1) \/ (y3 = y2)) /\ (~ (real_le y1 y3))) /\ (((y4 = y1) \/ (y4 = y2)) /\ (~ (real_le y2 y4)))) y0.
Definition term162 (x0 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((real_le y2 x0) /\ (real_le y2 y1))) y0.
Definition term61 (x0 : real) (x1 : real) := real_le (real_min x0 x1) (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))).
Definition term371 (x0 : real) (x1 : real) := exists y0 : real, (exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 x1)))).
Definition term352 (x0 : real) := exists y0 : real, (exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 y0)))).
Definition term315 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term240 (x0 : real) (x1 : real) (x2 : real) := or (~ ((x1 = x0) \/ (x1 = x2))).
Definition term359 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))) x2.
Definition term429 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term393 (x0 : real) (x1 : real) (x2 : real) := ((~ (x1 = x0)) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x1 x2)))) /\ ((~ (x1 = x2)) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x1 x2)))).
Definition term249 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ ((real_le y0 x0) /\ (real_le y0 x1))) x2.
Definition term107 (x0 : real) (x1 : real) := (x1 = x0) \/ (@IN real x1 (@EMPTY real)).
Definition term271 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term106 (x0 : real) (x1 : real) := @IN real x0 (@INSERT real x1 (@EMPTY real)).
Definition term262 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))) x0).
Definition term232 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) x0).
Definition term305 (x0 : real) (x1 : real) := fun y0 : real => exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1))).
Definition term149 (x0 : real) := fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0)).
Definition term245 (x0 : real -> Prop) := ~ (ex x0).
Definition term349 (x0 : real) (x1 : real) := (exists y0 : real, exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))) \/ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1)))).
Definition term60 (x0 : real) (x1 : real) := (real_le (real_min x0 x1) (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))) /\ (real_le (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) (real_min x0 x1)).
Definition term164 (x0 : real) := forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0)).
Definition term284 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => ((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x1 y0))) x0) /\ (exists y0 : real, ((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0))).
Definition term94 (x0 : real) := fun y0 : real => (real_min x0 y0) = (inf (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))).
Definition term121 (x0 : real) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x1 y0.
Definition term115 (x0 : real) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) -> real_le x1 y0.
Definition term125 (x0 : real) (x1 : real) := and ((forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x0 y0) \/ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0)).
Definition term83 (x0 : real) (x1 : real) := and ((forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x0 y0) \/ (forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x1 y0)).
Definition term380 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := or ((fun y0 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0)))) x3).
Definition term49 (x0 : real) (x1 : real -> Prop) := real_le x0 (inf x1).
Definition term198 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term15 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term34 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, ~ ((@INSERT a0 x0 y0) = (@EMPTY a0)).
Definition term252 (x0 : real) (x1 : real) := fun y0 : real => ((~ (y0 = x0)) /\ (~ (y0 = x1))) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1))).
Definition term443 (x0 : real) (x1 : real) := ((x0 = x0) /\ (real_le x0 x0)) -> ~ (real_le x0 x1).
Definition term202 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term144 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term250 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ ((real_le y0 x0) /\ (real_le y0 x1))) x2).
Definition term215 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0) x2).
Definition term206 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((y0 = x1) \/ (y0 = x0)) -> real_le x1 y0) x2).
Definition term397 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term172 (x0 : real) := (fun y0 : real => forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) x0.
Definition term57 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0))) x0.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((@INSERT a0 x0 x1) = (@EMPTY a0)).
Definition term165 (x0 : real) := (forall y0 : real, (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)) /\ (forall y0 : real, exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0))).
Definition term354 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term385 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => ((((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0)))) \/ (forall y1 : real, ((~ (y1 = x1)) /\ (~ (y1 = x2))) \/ ((~ (real_le y1 x1)) \/ (~ (real_le y1 x2)))).
Definition term120 (x0 : real) (x1 : real) (x2 : real) := ((x2 = x0) \/ (x2 = x1)) -> real_le x1 x2.
Definition term43 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @FINITE a0 (@INSERT a0 x0 x1).
Definition term46 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le y0 (inf x0)) = (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)) x1.
Definition term426 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x1 = x0)) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x1 x2)))).
Definition term50 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le x1 y0.
Definition term166 := fun y0 : real => (forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))).
Definition term403 (x0 : real) := fun y0 : real => ~ (real_le x0 y0).
Definition term136 := (~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> False.
Definition term158 (x0 : real) := forall y0 : real, (fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0.
Definition term62 (x0 : real) (x1 : real) := (real_le x0 (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))) \/ (real_le x1 (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real))))).
Definition term108 (x0 : real) (x1 : real) := or (x0 = x1).
Definition term229 (x0 : real) := exists y0 : real, (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le y0 y1))).
Definition term196 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term176 := fun y0 : real => ((fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0) /\ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((real_le y3 y1) /\ (real_le y3 y2))) y0).
Definition term154 (x0 : real) := fun y0 : real => ((fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0) /\ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((real_le y2 x0) /\ (real_le y2 y1))) y0).
Definition term411 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term282 (x0 : real) (x1 : real) (x2 : real) := and ((fun y0 : real => ((y0 = x1) \/ (y0 = x0)) /\ (~ (real_le x1 y0))) x2).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0)) x1.
Definition term128 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ ((real_le y0 x0) /\ (real_le y0 x1)).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0))) x2.
Definition term84 (x0 : real) (x1 : real) := ((@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (~ ((@INSERT real x0 (@INSERT real x1 (@EMPTY real))) = (@EMPTY real)))) -> (real_le (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) (real_min x0 x1)) = (exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le y0 (real_min x0 x1))).
Definition term170 := fun y0 : real => forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2).
Definition term133 := fun y0 : real => forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))).
Definition term99 := fun y0 : real => forall y1 : real, ((forall y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) -> real_le y0 y2) \/ (forall y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) -> real_le y1 y2)) /\ (exists y2 : real, (@IN real y2 (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))) /\ ((real_le y2 y0) /\ (real_le y2 y1))).
Definition term11 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term223 (x0 : real) (x1 : real) := ~ ((forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x0 y0) \/ (forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0)).
Definition term188 := ~ ((forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1)))).
Definition term341 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 y0)))) x1.
Definition term28 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le (real_min x0 y0) y1) = ((real_le x0 y1) \/ (real_le y0 y1))) x1.
Definition term21 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le y1 (real_min x0 y0)) = ((real_le y1 x0) /\ (real_le y1 y0))) x1.
Definition term435 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term381 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := or ((((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((x3 = x1) \/ (x3 = x2)) /\ (~ (real_le x2 x3)))).
Definition term87 (x0 : real) (x1 : real) (x2 : real) := and (@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))).
Definition term132 (x0 : real) := forall y0 : real, ((forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0))).
Definition term97 (x0 : real) := forall y0 : real, ((forall y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) -> real_le x0 y1) \/ (forall y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) -> real_le y0 y1)) /\ (exists y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) /\ ((real_le y1 x0) /\ (real_le y1 y0))).
Definition term365 (x0 : real) (x1 : real) (x2 : real) := or ((fun y0 : real => exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))) x2).
Definition term438 (x0 : real) (x1 : real) := (x0 = x1) /\ (real_le x0 x1).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((@INSERT a0 x0 x1) = (@EMPTY a0))) -> ((@INSERT a0 x0 x1) = (@EMPTY a0)) = False.
Definition term71 (x0 : real) (x1 : real) := and (@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))).
Definition term214 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0) x2.
Definition term205 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((y0 = x1) \/ (y0 = x0)) -> real_le x1 y0) x2.
Definition term409 (x0 : real) := (real_le x0 x0) -> ~ (real_le x0 x0).
Definition term228 (x0 : real) := fun y0 : real => (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le y0 y1))).
Definition term336 (x0 : real) := exists y0 : real, ((fun y1 : real => exists y2 : real, exists y3 : real, (((y2 = x0) \/ (y2 = y1)) /\ (~ (real_le x0 y2))) /\ (((y3 = x0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) y0) \/ ((fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 x0)) \/ (~ (real_le y2 y1)))) y0).
Definition term318 := exists y0 : real, ((fun y1 : real => exists y2 : real, exists y3 : real, exists y4 : real, (((y3 = y1) \/ (y3 = y2)) /\ (~ (real_le y1 y3))) /\ (((y4 = y1) \/ (y4 = y2)) /\ (~ (real_le y2 y4)))) y0) \/ ((fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ ((~ (real_le y3 y1)) \/ (~ (real_le y3 y2)))) y0).
Definition term405 (x0 : real) := (fun y0 : real => ~ (real_le x0 y0)) x0.
Definition term54 (x0 : real -> Prop) (x1 : real) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (real_le (inf x0) x1) = (exists y0 : real, (@IN real y0 x0) /\ (real_le y0 x1)).
Definition term333 := fun y0 : real => (exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) \/ (exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1)))).
Definition term272 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term374 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0)))) x3.
Definition term241 (x0 : real) (x1 : real) (x2 : real) := or ((~ (x1 = x0)) /\ (~ (x1 = x2))).
Definition term210 (x0 : real) (x1 : real) (x2 : real) := ~ (((x2 = x0) \/ (x2 = x1)) -> real_le x1 x2).
Definition term199 (x0 : real) (x1 : real) (x2 : real) := ~ (((x2 = x1) \/ (x2 = x0)) -> real_le x1 x2).
Definition term383 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((((x0 = x2) \/ (x0 = x3)) /\ (~ (real_le x2 x0))) /\ (((x1 = x2) \/ (x1 = x3)) /\ (~ (real_le x3 x1)))) \/ (forall y0 : real, ((~ (y0 = x2)) /\ (~ (y0 = x3))) \/ ((~ (real_le y0 x2)) \/ (~ (real_le y0 x3)))).
Definition term66 (x0 : real) (x1 : real -> Prop) := (@FINITE real x1) -> (@FINITE real (@INSERT real x0 x1)) = True.
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@FINITE a0 (@INSERT a0 x0 x1)) = True.
Definition term442 (x0 : real) := (x0 = x0) /\ (real_le x0 x0).
Definition term211 (x0 : real) (x1 : real) (x2 : real) := ((x2 = x0) \/ (x2 = x1)) /\ (~ (real_le x1 x2)).
Definition term236 (x0 : real) (x1 : real) (x2 : real) := ~ ((x1 = x0) \/ (x1 = x2)).
Definition term256 (x0 : real) (x1 : real) := ~ ((fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0))) x1).
Definition term391 := fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, ((((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) \/ (forall y4 : real, ((~ (y4 = y0)) /\ (~ (y4 = y1))) \/ ((~ (real_le y4 y0)) \/ (~ (real_le y4 y1)))).
Definition term389 (x0 : real) := fun y0 : real => exists y1 : real, exists y2 : real, ((((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) \/ (forall y3 : real, ((~ (y3 = x0)) /\ (~ (y3 = y0))) \/ ((~ (real_le y3 x0)) \/ (~ (real_le y3 y0)))).
Definition term309 := fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3))).
Definition term307 (x0 : real) := fun y0 : real => exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2))).
Definition term102 (x0 : real) (x1 : real) (x2 : real -> Prop) := @IN real x0 (@INSERT real x1 x2).
Definition term400 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term39 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1)) x0.
Definition term382 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((fun y0 : real => (((x0 = x2) \/ (x0 = x3)) /\ (~ (real_le x2 x0))) /\ (((y0 = x2) \/ (y0 = x3)) /\ (~ (real_le x3 y0)))) x1) \/ (forall y0 : real, ((~ (y0 = x2)) /\ (~ (y0 = x3))) \/ ((~ (real_le y0 x2)) \/ (~ (real_le y0 x3)))).
Definition term167 := forall y0 : real, (forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))).
Definition term424 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ ((~ (x1 = x2)) \/ (~ (real_le x1 x2))).
Definition term401 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x1 x2))).
Definition term105 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) \/ (@IN real x1 (@INSERT real x2 (@EMPTY real))).
Definition term431 (x0 : real) (x1 : real) := ~ ((~ (x0 = x1)) \/ (~ (real_le x0 x1))).
Definition term123 (x0 : real) (x1 : real) := forall y0 : real, ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0.
Definition term117 (x0 : real) (x1 : real) := forall y0 : real, ((y0 = x1) \/ (y0 = x0)) -> real_le x1 y0.
Definition term80 (x0 : real) (x1 : real) := forall y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) -> real_le x1 y0.
Definition term75 (x0 : real) (x1 : real) := forall y0 : real, (@IN real y0 (@INSERT real x1 (@INSERT real x0 (@EMPTY real)))) -> real_le x1 y0.
Definition term407 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => ~ (real_le x0 y0)) x1).
Definition term279 (x0 : real) (x1 : real) := and (exists y0 : real, (fun y1 : real => ((y1 = x1) \/ (y1 = x0)) /\ (~ (real_le x1 y1))) y0).
Definition term375 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => (fun y1 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1)))) y0.
Definition term48 (x0 : real -> Prop) := (@FINITE real x0) /\ (~ (x0 = (@EMPTY real))).
Definition term185 := forall y0 : real, (fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((real_le y3 y1) /\ (real_le y3 y2))) y0.
Definition term180 := forall y0 : real, (fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0.
Definition term163 (x0 : real) := forall y0 : real, (fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((real_le y2 x0) /\ (real_le y2 y1))) y0.
Definition term88 (x0 : real) (x1 : real) (x2 : real) := (@IN real x0 (@INSERT real x1 (@INSERT real x2 (@EMPTY real)))) /\ (real_le x0 (real_min x1 x2)).
Definition term304 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0))).
Definition term153 (x0 : real) (x1 : real) := ((fun y0 : real => (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)) x1) /\ ((fun y0 : real => exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0))) x1).
Definition term436 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term25 (x0 : real) (x1 : real) (x2 : real) := (real_le x1 x0) /\ (real_le x1 x2).
Definition term299 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (exists y0 : real, ((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0)))).
Definition term298 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (exists y0 : real, (fun y1 : real => ((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1))) y0)).
Definition term31 (x0 : real) (x1 : real) (x2 : real) := real_le (real_min x0 x1) x2.
Definition term323 (x0 : real) := (fun y0 : real => exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1)))) x0.
Definition term319 (x0 : real) := (fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) x0.
Definition term175 (x0 : real) := ((fun y0 : real => forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) x0) /\ ((fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))) x0).
Definition term422 (x0 : real) := ~ (x0 = x0).
Definition term275 (x0 : real) (x1 : real) := exists y0 : real, ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) y0) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1))).
Definition term288 (x0 : real) (x1 : real) := exists y0 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1))).
Definition term73 (x0 : real) (x1 : real) := (@FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (~ ((@INSERT real x0 (@INSERT real x1 (@EMPTY real))) = (@EMPTY real))).
Definition term396 (x0 : real) (x1 : real) := forall y0 : real, ((~ (y0 = x0)) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1)))) /\ ((~ (y0 = x1)) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1)))).
Definition term268 := (~ (forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2))) \/ (~ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1)))).
Definition term427 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x1 = x0)) \/ (~ (real_le x1 x0)))) -> ~ (real_le x1 x2).
Definition term248 (x0 : real) (x1 : real) := forall y0 : real, ~ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ ((real_le y1 x0) /\ (real_le y1 x1))) y0).
Definition term194 := (~ ((forall y0 : real, forall y1 : real, (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (forall y0 : real, forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term251 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) /\ ((real_le y1 x0) /\ (real_le y1 x1))) y0).
Definition term227 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0).
Definition term216 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((y1 = x0) \/ (y1 = x1)) -> real_le x1 y1) y0).
Definition term207 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((y1 = x1) \/ (y1 = x0)) -> real_le x1 y1) y0).
Definition term428 (x0 : real) (x1 : real) := (~ (x0 = x1)) \/ (~ (real_le x0 x1)).
Definition term70 (x0 : real) (x1 : real) := @FINITE real (@INSERT real x0 (@INSERT real x1 (@EMPTY real))).
Definition term145 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term219 (x0 : real) (x1 : real) := and (~ (forall y0 : real, ((y0 = x1) \/ (y0 = x0)) -> real_le x1 y0)).
Definition term2 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term402 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x2)) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x1 x2))).
Definition term90 (x0 : real) (x1 : real) := fun y0 : real => (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ (real_le y0 (real_min x0 x1)).
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term64 (x0 : real) (x1 : real) := @INSERT real x0 (@INSERT real x1 (@EMPTY real)).
Definition term287 (x0 : real) (x1 : real) := fun y0 : real => (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1))).
Definition term122 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x0) \/ (y0 = x1)) -> real_le x1 y0.
Definition term116 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x1) \/ (y0 = x0)) -> real_le x1 y0.
Definition term29 (x0 : real) (x1 : real) := forall y0 : real, (real_le (real_min x0 x1) y0) = ((real_le x0 y0) \/ (real_le x1 y0)).
Definition term14 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term270 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term139 := ((~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term384 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => ((fun y1 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1)))) y0) \/ (forall y1 : real, ((~ (y1 = x1)) /\ (~ (y1 = x2))) \/ ((~ (real_le y1 x1)) \/ (~ (real_le y1 x2)))).
Definition term369 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => exists y2 : real, (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = x1)) /\ (~ (real_le x1 y2)))) y0) \/ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = x1))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 x1)))).
Definition term434 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term141 := (((~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> ((~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term395 (x0 : real) (x1 : real) := fun y0 : real => ((~ (y0 = x0)) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1)))) /\ ((~ (y0 = x1)) \/ ((~ (real_le y0 x0)) \/ (~ (real_le y0 x1)))).
Definition term79 (x0 : real) (x1 : real) := real_le x1 (inf (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))).
Definition term217 (x0 : real) (x1 : real) := fun y0 : real => ((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x1 y0)).
Definition term151 (x0 : real) (x1 : real) := and ((fun y0 : real => (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)) x1).
Definition term334 := exists y0 : real, (exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) \/ (exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1)))).
Definition term425 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term449 (x0 : real) (x1 : real) (x2 : real) := (x1 = x2) /\ ((real_le x1 x0) /\ (real_le x1 x2)).
Definition term55 (x0 : real -> Prop) (x1 : real) := real_le (inf x0) x1.
Definition term131 (x0 : real) := fun y0 : real => ((forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le x0 y1) \/ (forall y1 : real, ((y1 = x0) \/ (y1 = y0)) -> real_le y0 y1)) /\ (exists y1 : real, ((y1 = x0) \/ (y1 = y0)) /\ ((real_le y1 x0) /\ (real_le y1 y0))).
Definition term95 (x0 : real) := fun y0 : real => ((forall y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) -> real_le x0 y1) \/ (forall y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) -> real_le y0 y1)) /\ (exists y1 : real, (@IN real y1 (@INSERT real x0 (@INSERT real y0 (@EMPTY real)))) /\ ((real_le y1 x0) /\ (real_le y1 y0))).
Definition term350 (x0 : real) := fun y0 : real => ((fun y1 : real => exists y2 : real, exists y3 : real, (((y2 = x0) \/ (y2 = y1)) /\ (~ (real_le x0 y2))) /\ (((y3 = x0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) y0) \/ ((fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 x0)) \/ (~ (real_le y2 y1)))) y0).
Definition term332 := fun y0 : real => ((fun y1 : real => exists y2 : real, exists y3 : real, exists y4 : real, (((y3 = y1) \/ (y3 = y2)) /\ (~ (real_le y1 y3))) /\ (((y4 = y1) \/ (y4 = y2)) /\ (~ (real_le y2 y4)))) y0) \/ ((fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ ((~ (real_le y3 y1)) \/ (~ (real_le y3 y2)))) y0).
Definition term416 (x0 : real) := (real_le x0 x0) -> False.
Definition term420 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term366 (x0 : real) (x1 : real) (x2 : real) := or (exists y0 : real, (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0)))).
Definition term38 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1).
Definition term4 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term32 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ (real_le x1 x2).
Definition term174 (x0 : real) := (fun y0 : real => forall y1 : real, exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))) x0.
Definition term26 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le (real_min y0 y1) y2) = ((real_le y0 y2) \/ (real_le y1 y2))) x0.
Definition term19 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le y2 (real_min y0 y1)) = ((real_le y2 y0) /\ (real_le y2 y1))) x0.
Definition term347 (x0 : real) (x1 : real) := or (exists y0 : real, exists y1 : real, (((y0 = x0) \/ (y0 = x1)) /\ (~ (real_le x0 y0))) /\ (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x1 y1)))).
Definition term329 (x0 : real) := or (exists y0 : real, exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))).
Definition term311 := or (exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))).
Definition term267 := or (exists y0 : real, exists y1 : real, (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y1 y2)))).
Definition term314 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term220 (x0 : real) (x1 : real) := and (exists y0 : real, ((y0 = x1) \/ (y0 = x0)) /\ (~ (real_le x1 y0))).
Definition term432 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) /\ (~ (~ (real_le x0 x1))).
Definition term168 := forall y0 : real, ((fun y1 : real => forall y2 : real, (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y1 y3) \/ (forall y3 : real, ((y3 = y1) \/ (y3 = y2)) -> real_le y2 y3)) y0) /\ ((fun y1 : real => forall y2 : real, exists y3 : real, ((y3 = y1) \/ (y3 = y2)) /\ ((real_le y3 y1) /\ (real_le y3 y2))) y0).
Definition term146 (x0 : real) := forall y0 : real, ((fun y1 : real => (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le x0 y2) \/ (forall y2 : real, ((y2 = x0) \/ (y2 = y1)) -> real_le y1 y2)) y0) /\ ((fun y1 : real => exists y2 : real, ((y2 = x0) \/ (y2 = y1)) /\ ((real_le y2 x0) /\ (real_le y2 y1))) y0).
Definition term413 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term129 (x0 : real) (x1 : real) := exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ ((real_le y0 x0) /\ (real_le y0 x1)).
Definition term92 (x0 : real) (x1 : real) := exists y0 : real, (@IN real y0 (@INSERT real x0 (@INSERT real x1 (@EMPTY real)))) /\ ((real_le y0 x0) /\ (real_le y0 x1)).
Definition term335 (x0 : real) := (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, (((y2 = x0) \/ (y2 = y1)) /\ (~ (real_le x0 y2))) /\ (((y3 = x0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) y0) \/ (exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 x0)) \/ (~ (real_le y2 y1)))) y0).
Definition term317 := (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, exists y4 : real, (((y3 = y1) \/ (y3 = y2)) /\ (~ (real_le y1 y3))) /\ (((y4 = y1) \/ (y4 = y2)) /\ (~ (real_le y2 y4)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ ((~ (real_le y3 y1)) \/ (~ (real_le y3 y2)))) y0).
Definition term398 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term189 := imp (~ (forall y0 : real, forall y1 : real, ((forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y0 y2) \/ (forall y2 : real, ((y2 = y0) \/ (y2 = y1)) -> real_le y1 y2)) /\ (exists y2 : real, ((y2 = y0) \/ (y2 = y1)) /\ ((real_le y2 y0) /\ (real_le y2 y1))))).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term410 (x0 : Prop) := x0 -> ~ x0.
Definition term98 := fun y0 : real => forall y1 : real, (real_min y0 y1) = (inf (@INSERT real y0 (@INSERT real y1 (@EMPTY real)))).
Definition term244 (x0 : real) (x1 : real) (x2 : real) := ~ (((x1 = x0) \/ (x1 = x2)) /\ ((real_le x1 x0) /\ (real_le x1 x2))).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term368 (x0 : real) (x1 : real) (x2 : real) := (exists y0 : real, (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ (((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0)))) \/ (forall y0 : real, ((~ (y0 = x1)) /\ (~ (y0 = x2))) \/ ((~ (real_le y0 x1)) \/ (~ (real_le y0 x2)))).
Definition term302 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ ((fun y1 : real => ((y1 = x1) \/ (y1 = x2)) /\ (~ (real_le x2 y1))) y0).
Definition term346 (x0 : real) (x1 : real) := or ((fun y0 : real => exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) x1).
Definition term300 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (((x0 = x1) \/ (x0 = x2)) /\ (~ (real_le x1 x0))) /\ ((fun y0 : real => ((y0 = x1) \/ (y0 = x2)) /\ (~ (real_le x2 y0))) x3).
Definition term114 (x0 : real) (x1 : real) (x2 : real) := ((x2 = x1) \/ (x2 = x0)) -> real_le x1 x2.
Definition term247 (x0 : real) (x1 : real) := ~ (exists y0 : real, ((y0 = x0) \/ (y0 = x1)) /\ ((real_le y0 x0) /\ (real_le y0 x1))).
Definition term361 (x0 : real) (x1 : real) := exists y0 : real, (fun y1 : real => exists y2 : real, (((y1 = x0) \/ (y1 = x1)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = x1)) /\ (~ (real_le x1 y2)))) y0.
Definition term343 (x0 : real) := exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 x0)) \/ (~ (real_le y2 y1)))) y0.
Definition term339 (x0 : real) := exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, (((y2 = x0) \/ (y2 = y1)) /\ (~ (real_le x0 y2))) /\ (((y3 = x0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) y0.
Definition term325 := exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ ((~ (real_le y3 y1)) \/ (~ (real_le y3 y2)))) y0.
Definition term321 := exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, exists y4 : real, (((y3 = y1) \/ (y3 = y2)) /\ (~ (real_le y1 y3))) /\ (((y4 = y1) \/ (y4 = y2)) /\ (~ (real_le y2 y4)))) y0.
Definition term345 (x0 : real) := @eq Prop ((exists y0 : real, exists y1 : real, exists y2 : real, (((y1 = x0) \/ (y1 = y0)) /\ (~ (real_le x0 y1))) /\ (((y2 = x0) \/ (y2 = y0)) /\ (~ (real_le y0 y2)))) \/ (exists y0 : real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (y1 = y0))) \/ ((~ (real_le y1 x0)) \/ (~ (real_le y1 y0))))).
Definition term344 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, (((y2 = x0) \/ (y2 = y1)) /\ (~ (real_le x0 y2))) /\ (((y3 = x0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) y0) \/ (exists y0 : real, (fun y1 : real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 x0)) \/ (~ (real_le y2 y1)))) y0)).
Definition term327 := @eq Prop ((exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, (((y2 = y0) \/ (y2 = y1)) /\ (~ (real_le y0 y2))) /\ (((y3 = y0) \/ (y3 = y1)) /\ (~ (real_le y1 y3)))) \/ (exists y0 : real, exists y1 : real, forall y2 : real, ((~ (y2 = y0)) /\ (~ (y2 = y1))) \/ ((~ (real_le y2 y0)) \/ (~ (real_le y2 y1))))).
Definition term326 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, exists y4 : real, (((y3 = y1) \/ (y3 = y2)) /\ (~ (real_le y1 y3))) /\ (((y4 = y1) \/ (y4 = y2)) /\ (~ (real_le y2 y4)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, forall y3 : real, ((~ (y3 = y1)) /\ (~ (y3 = y2))) \/ ((~ (real_le y3 y1)) \/ (~ (real_le y3 y2)))) y0)).
