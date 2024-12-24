Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term174 (x0 : real -> Prop) := (~ (exists y0 : real, @IN real y0 x0)) \/ (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)).
Definition term314 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) /\ (exists y1 : real -> real, forall y2 : real, ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ ((((y1 y2) = x0) \/ (@IN real (y1 y2) x1)) /\ (~ (real_le y2 (y1 y2))))).
Definition term91 (x0 : real) (x1 : real) (x2 : real -> Prop) := imp ((x1 = x0) \/ (@IN real x1 x2)).
Definition term21 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, ~ ((@INSERT a0 y0 y1) = (@EMPTY a0))) x0.
Definition term76 (x0 : real -> Prop) := (@FINITE real x0) -> (fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) x0.
Definition term500 (x0 : real -> real) (x1 : real) (x2 : real) := (~ (x1 = x2)) \/ ((x0 x1) = x2).
Definition term493 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))))).
Definition term442 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term479 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (@IN real x1 x2) /\ (~ (@IN real (x0 x1) x2)).
Definition term205 (x0 : real) (x1 : real -> Prop) := (((exists y0 : real, @IN real y0 x1) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) /\ (~ (exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1))).
Definition term539 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x1 x0) /\ (~ (real_le x1 x2))).
Definition term412 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := imp ((x2 = x0) /\ (~ (@IN real (x1 x2) x3))).
Definition term228 (x0 : real -> Prop) := exists y0 : real, (forall y1 : real, ~ (@IN real y1 x0)) \/ ((fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2))) y0).
Definition term208 (x0 : type1022) := ~ (all x0).
Definition term182 (x0 : real -> Prop) := ~ (all x0).
Definition term425 (x0 : real -> real) (x1 : real) := (~ (real_le (x0 x1) (x0 x1))) -> real_le (x0 x1) (x0 x1).
Definition term457 := (~ False) -> False.
Definition term34 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term322 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) := (fun y0 : real -> real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ ((((y0 y1) = x0) \/ (@IN real (y0 y1) x1)) /\ (~ (real_le y1 (y0 y1))))) x2.
Definition term72 := ((~ ((@EMPTY real) = (@EMPTY real))) -> exists y0 : real, (@IN real y0 (@EMPTY real)) /\ (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1)) /\ (forall y0 : real, forall y1 : real -> Prop, (((~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (~ ((@INSERT real y0 y1) = (@EMPTY real))) -> exists y2 : real, (@IN real y2 (@INSERT real y0 y1)) /\ (forall y3 : real, (@IN real y3 (@INSERT real y0 y1)) -> real_le y2 y3)).
Definition term133 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2).
Definition term286 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ (((y2 = x0) \/ (@IN real y2 x1)) /\ (~ (real_le y1 y2)))) x2 y0.
Definition term433 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (real_le x0 x1))))) -> real_le x2 x3.
Definition term538 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x1 x0)) \/ (real_le x1 x2))).
Definition term416 (x0 : real -> real) (x1 : real) := (~ ((x0 x1) = x1)) -> (x0 x1) = x1.
Definition term311 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((fun y0 : real => ((forall y1 : real, ~ (@IN real y1 x2)) \/ ((@IN real y0 x2) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) x0) /\ (exists y0 : real -> real, forall y1 : real, ((~ (y1 = x1)) /\ (~ (@IN real y1 x2))) \/ ((((y0 y1) = x1) \/ (@IN real (y0 y1) x2)) /\ (~ (real_le y1 (y0 y1))))).
Definition term449 (x0 : real -> real) (x1 : real) := (~ (real_le x1 (x0 x1))) -> real_le x1 (x0 x1).
Definition term340 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le x0 x1) /\ (real_le x1 x2))).
Definition term514 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (~ (@IN real (x0 x1) x2)) -> @IN real (x0 x1) x2.
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1))) x1.
Definition term35 (x0 : real -> Prop) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term261 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ (exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le x2 y1))) y0).
Definition term328 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real -> real) := (((forall y0 : real, ~ (@IN real y0 x2)) \/ ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ (forall y0 : real, ((~ (y0 = x1)) /\ (~ (@IN real y0 x2))) \/ ((((x3 y0) = x1) \/ (@IN real (x3 y0) x2)) /\ (~ (real_le y0 (x3 y0))))).
Definition term284 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (fun y0 : real => ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ (((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0)))) x3.
Definition term264 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => (fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le x2 y1))) y0.
Definition term92 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (@IN real x3 (@INSERT real x0 x1)) -> real_le x2 x3.
Definition term419 (x0 : real -> real) (x1 : real) := ~ ((x0 x1) = (x0 x1)).
Definition term101 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1).
Definition term353 (x0 : real -> real) (x1 : real) := ~ (real_le x1 (x0 x1)).
Definition term39 := fun y0 : real -> Prop => ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2).
Definition term406 (x0 : Prop) := ~ (~ x0).
Definition term531 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le x0 x1)) \/ (real_le x0 x2))) -> ~ (real_le x1 x2).
Definition term374 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2)).
Definition term246 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((fun y1 : real => (forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) y0) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term211 (x0 : real) := exists y0 : real -> Prop, ~ ((fun y1 : real -> Prop => (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real x0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = x0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = x0) \/ (@IN real y3 y1)) -> real_le y2 y3)) y0).
Definition term522 (x0 : real) (x1 : real -> real) (x2 : real) := ~ (real_le x0 (x1 x2)).
Definition term461 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (~ (~ (@IN real x2 x0))) -> ~ (real_le x2 (x1 x2)).
Definition term169 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) /\ (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le x1 y0)).
Definition term153 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term410 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := (x2 = x0) /\ (~ (@IN real (x1 x2) x3)).
Definition term370 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0)) x2.
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term430 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_le x1 x2)).
Definition term399 (x0 : real -> real) (x1 : real -> Prop) (x2 : real) (x3 : real) := @eq Prop (((x0 x2) = x3) \/ ((@IN real (x0 x2) x1) \/ (~ (x2 = x3)))).
Definition term438 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x2 = x0))) /\ (~ (~ (real_le x1 x2))).
Definition term210 (x0 : real) := ~ (forall y0 : real -> Prop, (((exists y1 : real, @IN real y1 y0) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> exists y1 : real, ((y1 = x0) \/ (@IN real y1 y0)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) -> real_le y1 y2)).
Definition term439 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term56 (x0 : real) (x1 : real -> Prop) := ((~ (x1 = (@EMPTY real))) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term93 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := ((x3 = x0) \/ (@IN real x3 x1)) -> real_le x2 x3.
Definition term255 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((fun y0 : real => (forall y1 : real, ~ (@IN real y1 x2)) \/ ((@IN real y0 x2) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y0 y1)))) x0) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2)).
Definition term467 (x0 : real) (x1 : real) (x2 : real -> Prop) := (~ (real_le x0 x1)) -> ~ (@IN real x1 x2).
Definition term140 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term195 (x0 : real) (x1 : real -> Prop) (x2 : real) := ~ (((x2 = x0) \/ (@IN real x2 x1)) /\ (forall y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) -> real_le x2 y0)).
Definition term119 (x0 : real) := fun y0 : real -> Prop => (((exists y1 : real, @IN real y1 y0) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> exists y1 : real, ((y1 = x0) \/ (@IN real y1 y0)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) -> real_le y1 y2).
Definition term106 (x0 : real) := fun y0 : real -> Prop => (((~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> exists y1 : real, ((y1 = x0) \/ (@IN real y1 y0)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) -> real_le y1 y2).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term230 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2))) y0.
Definition term180 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := ~ (((x3 = x0) \/ (@IN real x3 x1)) -> real_le x2 x3).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term50 (x0 : real -> Prop) := (fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) x0.
Definition term317 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term123 (x0 : Prop) := (~ x0) -> False.
Definition term497 (x0 : real -> real) (x1 : real) := ((x0 x1) = (x0 x1)) /\ ((~ (real_le x1 (x0 x1))) /\ (real_le (x0 x1) (x0 x1))).
Definition term351 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) (x3 : real) := (((~ (x3 = x0)) /\ (~ (@IN real x3 x1))) \/ (((x2 x3) = x0) \/ (@IN real (x2 x3) x1))) /\ (((~ (x3 = x0)) /\ (~ (@IN real x3 x1))) \/ (~ (real_le x3 (x2 x3)))).
Definition term184 (x0 : real) (x1 : real -> Prop) (x2 : real) := ~ (forall y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) -> real_le x2 y0).
Definition term532 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ (real_le x1 x2).
Definition term166 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x2 x0)) \/ (real_le x1 x2).
Definition term486 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3)))).
Definition term121 := fun y0 : real => forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3).
Definition term108 := fun y0 : real => forall y1 : real -> Prop, (((~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3).
Definition term98 (x0 : real) (x1 : real -> Prop) (x2 : real) := (@IN real x2 (@INSERT real x0 x1)) /\ (forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> real_le x2 y0).
Definition term300 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, ((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) /\ (exists y0 : real -> real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ ((((y0 y1) = x0) \/ (@IN real (y0 y1) x1)) /\ (~ (real_le y1 (y0 y1))))).
Definition term89 (x0 : real) (x1 : real) (x2 : real -> Prop) := and ((x1 = x0) \/ (@IN real x1 x2)).
Definition term244 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term138 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term113 (x0 : real -> Prop) := imp (exists y0 : real, @IN real y0 x0).
Definition term9 (a0 : Type') := fun y0 : a0 -> Prop => (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0))).
Definition term296 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) := forall y0 : real, ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ ((((x2 y0) = x0) \/ (@IN real (x2 y0) x1)) /\ (~ (real_le y0 (x2 y0)))).
Definition term66 (x0 : real) := forall y0 : real -> Prop, (((~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> (~ ((@INSERT real x0 y0) = (@EMPTY real))) -> exists y1 : real, (@IN real y1 (@INSERT real x0 y0)) /\ (forall y2 : real, (@IN real y2 (@INSERT real x0 y0)) -> real_le y1 y2).
Definition term318 (x0 : Prop) (x1 : type1028) := x0 /\ (exists y0 : real -> real, x1 y0).
Definition term165 (x0 : real -> Prop) := forall y0 : real, ~ (@IN real y0 x0).
Definition term323 (x0 : real) (x1 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ ((((y1 y2) = x0) \/ (@IN real (y1 y2) x1)) /\ (~ (real_le y2 (y1 y2))))) y0.
Definition term74 := imp (((~ ((@EMPTY real) = (@EMPTY real))) -> exists y0 : real, (@IN real y0 (@EMPTY real)) /\ (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1)) /\ (forall y0 : real, forall y1 : real -> Prop, (((~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (~ ((@INSERT real y0 y1) = (@EMPTY real))) -> exists y2 : real, (@IN real y2 (@INSERT real y0 y1)) /\ (forall y3 : real, (@IN real y3 (@INSERT real y0 y1)) -> real_le y2 y3))).
Definition term65 (x0 : real) := forall y0 : real -> Prop, (((fun y1 : real -> Prop => (~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) y0) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> (fun y1 : real -> Prop => (~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) (@INSERT real x0 y0).
Definition term295 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ (((y2 = x0) \/ (@IN real y2 x1)) /\ (~ (real_le y1 y2)))) y0 (x2 y0).
Definition term400 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term292 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) (x3 : real) := ((~ (x3 = x0)) /\ (~ (@IN real x3 x1))) \/ ((((x2 x3) = x0) \/ (@IN real (x2 x3) x1)) /\ (~ (real_le x3 (x2 x3)))).
Definition term470 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (~ (@IN real x1 x2)) \/ (@IN real (x0 x1) x2).
Definition term59 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) (@INSERT real x0 x1).
Definition term267 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop (((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ (exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0)))).
Definition term266 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop (((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ (exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le x2 y1))) y0)).
Definition term360 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := and (((~ (x2 = x0)) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3))) /\ ((~ (@IN real x2 x3)) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3)))).
Definition term287 (x0 : real) (x1 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ (((y3 = x0) \/ (@IN real y3 x1)) /\ (~ (real_le y2 y3)))) y0 y1.
Definition term117 (x0 : real) (x1 : real -> Prop) := imp (((exists y0 : real, @IN real y0 x1) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))).
Definition term58 (x0 : real) (x1 : real -> Prop) := imp (((~ (x1 = (@EMPTY real))) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))).
Definition term53 (x0 : real -> Prop) := and ((~ (x0 = (@EMPTY real))) -> exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)).
Definition term49 := and ((~ ((@EMPTY real) = (@EMPTY real))) -> exists y0 : real, (@IN real y0 (@EMPTY real)) /\ (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1)).
Definition term14 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2))) x0.
Definition term335 (x0 : real) := exists y0 : real -> Prop, exists y1 : real, exists y2 : real -> real, (((forall y3 : real, ~ (@IN real y3 y0)) \/ ((@IN real y1 y0) /\ (forall y3 : real, (~ (@IN real y3 y0)) \/ (real_le y1 y3)))) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) /\ (forall y3 : real, ((~ (y3 = x0)) /\ (~ (@IN real y3 y0))) \/ ((((y2 y3) = x0) \/ (@IN real (y2 y3) y0)) /\ (~ (real_le y3 (y2 y3))))).
Definition term186 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) -> real_le x2 y0) x3.
Definition term316 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term63 (x0 : real) := fun y0 : real -> Prop => (((fun y1 : real -> Prop => (~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) y0) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> (fun y1 : real -> Prop => (~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) (@INSERT real x0 y0).
Definition term112 (x0 : real -> Prop) := imp (~ (x0 = (@EMPTY real))).
Definition term334 (x0 : real) := fun y0 : real -> Prop => exists y1 : real, exists y2 : real -> real, (((forall y3 : real, ~ (@IN real y3 y0)) \/ ((@IN real y1 y0) /\ (forall y3 : real, (~ (@IN real y3 y0)) \/ (real_le y1 y3)))) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) /\ (forall y3 : real, ((~ (y3 = x0)) /\ (~ (@IN real y3 y0))) \/ ((((y2 y3) = x0) \/ (@IN real (y2 y3) y0)) /\ (~ (real_le y3 (y2 y3))))).
Definition term386 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term99 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((x2 = x0) \/ (@IN real x2 x1)) /\ (forall y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) -> real_le x2 y0).
Definition term213 (x0 : real) (x1 : real -> Prop) := ~ ((fun y0 : real -> Prop => (((exists y1 : real, @IN real y1 y0) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> exists y1 : real, ((y1 = x0) \/ (@IN real y1 y0)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) -> real_le y1 y2)) x1).
Definition term450 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term343 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term477 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (~ (~ (@IN real x1 x2))) /\ (~ (@IN real (x0 x1) x2)).
Definition term388 (x0 : Prop) := (~ x0) -> x0.
Definition term104 (x0 : real) (x1 : real -> Prop) := True -> exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1).
Definition term517 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((real_le x0 x1) \/ (~ (@IN real x1 x2))).
Definition term127 := ((~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term40 := fun y0 : real -> Prop => (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2).
Definition term482 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) (x3 : real) := ((@IN real x2 x0) /\ (~ (@IN real (x1 x2) x0))) -> (x1 x2) = x3.
Definition term413 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) (x3 : real) := ((x2 = x3) /\ (~ (@IN real (x1 x2) x0))) -> (x1 x2) = x3.
Definition term403 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term540 (x0 : real) (x1 : real) (x2 : real) := ((real_le x0 x1) /\ (~ (real_le x0 x2))) -> ~ (real_le x1 x2).
Definition term275 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term512 (x0 : real -> real) (x1 : real) := (x1 = x1) /\ (~ ((x0 x1) = x1)).
Definition term206 (x0 : real) (x1 : real -> Prop) := (((forall y0 : real, ~ (@IN real y0 x1)) \/ (exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) /\ (forall y0 : real, ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (exists y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1)))).
Definition term214 (x0 : real) := fun y0 : real -> Prop => ~ ((fun y1 : real -> Prop => (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real x0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = x0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = x0) \/ (@IN real y3 y1)) -> real_le y2 y3)) y0).
Definition term528 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2))).
Definition term303 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => ((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) x2.
Definition term179 (x0 : real) (x1 : real) (x2 : real -> Prop) := (~ (x1 = x0)) /\ (~ (@IN real x1 x2)).
Definition term254 (x0 : real -> Prop) (x1 : real) := and ((forall y0 : real, ~ (@IN real y0 x0)) \/ ((@IN real x1 x0) /\ (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le x1 y0)))).
Definition term305 (x0 : real) (x1 : real -> Prop) := exists y0 : real, (fun y1 : real => ((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) y0.
Definition term265 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real, (fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le x2 y1))) y0.
Definition term249 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => (forall y2 : real, ~ (@IN real y2 x0)) \/ ((@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)))) y0.
Definition term231 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2))) y0.
Definition term100 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) /\ (forall y1 : real, (@IN real y1 (@INSERT real x0 x1)) -> real_le y0 y1).
Definition term451 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term350 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term348 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term148 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term146 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term132 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term122 := forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3).
Definition term109 := forall y0 : real, forall y1 : real -> Prop, (((~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3).
Definition term70 := forall y0 : real, forall y1 : real -> Prop, (((~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (~ ((@INSERT real y0 y1) = (@EMPTY real))) -> exists y2 : real, (@IN real y2 (@INSERT real y0 y1)) /\ (forall y3 : real, (@IN real y3 (@INSERT real y0 y1)) -> real_le y2 y3).
Definition term69 := forall y0 : real, forall y1 : real -> Prop, (((fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) y1) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) (@INSERT real y0 y1).
Definition term476 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := ~ ((~ (@IN real x1 x2)) \/ (@IN real (x0 x1) x2)).
Definition term229 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1))) x1.
Definition term494 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x3 = x1) /\ ((~ (real_le x0 x1)) /\ (real_le x2 x3))).
Definition term529 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term299 (x0 : real) (x1 : real -> Prop) := exists y0 : real -> real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ ((((y0 y1) = x0) \/ (@IN real (y0 y1) x1)) /\ (~ (real_le y1 (y0 y1)))).
Definition term280 (x0 : real) (x1 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ (((y3 = x0) \/ (@IN real y3 x1)) /\ (~ (real_le y2 y3)))) y1 (y0 y1).
Definition term278 (x0 : type1626) := exists y0 : real -> real, forall y1 : real, x0 y1 (y0 y1).
Definition term499 (x0 : real -> real) (x1 : real) := ((x0 x1) = x1) -> ~ ((x0 x1) = x1).
Definition term487 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x3 = x1))) /\ (~ ((real_le x0 x1) \/ (~ (real_le x2 x3)))).
Definition term110 := True /\ (forall y0 : real, forall y1 : real -> Prop, (((~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3)).
Definition term337 := exists y0 : real, exists y1 : real -> Prop, exists y2 : real, exists y3 : real -> real, (((forall y4 : real, ~ (@IN real y4 y1)) \/ ((@IN real y2 y1) /\ (forall y4 : real, (~ (@IN real y4 y1)) \/ (real_le y2 y4)))) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) /\ (forall y4 : real, ((~ (y4 = y0)) /\ (~ (@IN real y4 y1))) \/ ((((y3 y4) = y0) \/ (@IN real (y3 y4) y1)) /\ (~ (real_le y4 (y3 y4))))).
Definition term333 (x0 : real) (x1 : real -> Prop) := exists y0 : real, exists y1 : real -> real, (((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y0 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y0 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) /\ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ ((((y1 y2) = x0) \/ (@IN real (y1 y2) x1)) /\ (~ (real_le y2 (y1 y2))))).
Definition term222 := exists y0 : real, exists y1 : real -> Prop, (((forall y2 : real, ~ (@IN real y2 y1)) \/ (exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y2 y3)))) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) /\ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (@IN real y2 y1))) \/ (exists y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) /\ (~ (real_le y2 y3)))).
Definition term157 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term134 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term257 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => (forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) y0) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term142 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term137 := (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term83 := False -> exists y0 : real, (@IN real y0 (@EMPTY real)) /\ (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1).
Definition term331 (x0 : real) (x1 : real) (x2 : real -> Prop) := exists y0 : real -> real, (((forall y1 : real, ~ (@IN real y1 x2)) \/ ((@IN real x0 x2) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le x0 y1)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ (forall y1 : real, ((~ (y1 = x1)) /\ (~ (@IN real y1 x2))) \/ ((((y0 y1) = x1) \/ (@IN real (y0 y1) x2)) /\ (~ (real_le y1 (y0 y1))))).
Definition term216 (x0 : real) := exists y0 : real -> Prop, (((forall y1 : real, ~ (@IN real y1 y0)) \/ (exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) /\ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 y0))) \/ (exists y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) /\ (~ (real_le y1 y2)))).
Definition term55 (x0 : real) (x1 : real -> Prop) := ((fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) x1) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term472 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ((x1 x2) = x0) \/ ((@IN real (x1 x2) x3) \/ (~ (@IN real x2 x3))).
Definition term319 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 /\ (x1 y0).
Definition term160 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => @IN real y0 x0) x1.
Definition term488 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term537 (x0 : real) (x1 : real) (x2 : real) := (real_le x1 x0) /\ (~ (real_le x1 x2)).
Definition term217 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real -> Prop, (((exists y3 : real, @IN real y3 y2) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) /\ ((~ (@IN real y1 y2)) /\ (@FINITE real y2))) -> exists y3 : real, ((y3 = y1) \/ (@IN real y3 y2)) /\ (forall y4 : real, ((y4 = y1) \/ (@IN real y4 y2)) -> real_le y3 y4)) y0).
Definition term185 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real, ~ ((fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) -> real_le x2 y1) y0).
Definition term48 := and ((fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) (@EMPTY real)).
Definition term469 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ((x1 x2) = x0) \/ ((~ (@IN real x2 x3)) \/ (@IN real (x1 x2) x3)).
Definition term393 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ((x1 x2) = x0) \/ ((~ (x2 = x0)) \/ (@IN real (x1 x2) x3)).
Definition term443 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3))).
Definition term248 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (forall y2 : real, ~ (@IN real y2 x0)) \/ ((@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)))) y0.
Definition term82 := exists y0 : real, (@IN real y0 (@EMPTY real)) /\ (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1).
Definition term511 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ((x2 = x0) /\ (~ ((x1 x2) = x0))) -> @IN real (x1 x2) x3.
Definition term391 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := @IN real (x0 x1) x2.
Definition term247 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (forall y1 : real, ~ (@IN real y1 x0)) \/ ((@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)))) x1.
Definition term521 (x0 : real) (x1 : real -> real) (x2 : real) := (~ (real_le x0 (x1 x2))) -> real_le x0 (x1 x2).
Definition term220 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real -> Prop, (((exists y3 : real, @IN real y3 y2) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) /\ ((~ (@IN real y1 y2)) /\ (@FINITE real y2))) -> exists y3 : real, ((y3 = y1) \/ (@IN real y3 y2)) /\ (forall y4 : real, ((y4 = y1) \/ (@IN real y4 y2)) -> real_le y3 y4)) y0).
Definition term262 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real, ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ ((fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le x2 y1))) y0).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (y0 = (@EMPTY a0))) = (exists y1 : a0, @IN a0 y1 y0)) x0.
Definition term44 := (((fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) (@EMPTY real)) /\ (forall y0 : real, forall y1 : real -> Prop, (((fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) y1) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) (@INSERT real y0 y1))) -> forall y0 : real -> Prop, (@FINITE real y0) -> (fun y1 : real -> Prop => (~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) y0.
Definition term88 (x0 : real) (x1 : real) (x2 : real -> Prop) := and (@IN real x0 (@INSERT real x1 x2)).
Definition term389 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := ~ (@IN real (x0 x1) x2).
Definition term504 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) (x3 : real) := (@IN real (x1 x2) x0) \/ (((x1 x2) = x3) \/ (~ (x2 = x3))).
Definition term533 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x1 x0)) \/ (real_le x1 x2)).
Definition term515 (x0 : real) (x1 : real) (x2 : real -> Prop) := (real_le x0 x1) \/ (~ (@IN real x1 x2)).
Definition term308 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, ((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) /\ (exists y0 : real -> real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ ((((y0 y1) = x0) \/ (@IN real (y0 y1) x1)) /\ (~ (real_le y1 (y0 y1)))))).
Definition term307 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => ((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) y0) /\ (exists y0 : real -> real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ ((((y0 y1) = x0) \/ (@IN real (y0 y1) x1)) /\ (~ (real_le y1 (y0 y1)))))).
Definition term130 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ~ ((@INSERT a0 x0 y0) = (@EMPTY a0))) x1.
Definition term384 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term78 := forall y0 : real -> Prop, (@FINITE real y0) -> (fun y1 : real -> Prop => (~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) y0.
Definition term544 (x0 : real) (x1 : real -> real) (x2 : real) := (real_le (x1 x0) (x1 x2)) -> ~ (real_le (x1 x0) (x1 x2)).
Definition term181 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := ((x3 = x0) \/ (@IN real x3 x1)) /\ (~ (real_le x2 x3)).
Definition term518 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (~ (@IN real x2 x0))) -> real_le x1 x2.
Definition term324 (x0 : real) (x1 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ ((((y1 y2) = x0) \/ (@IN real (y1 y2) x1)) /\ (~ (real_le y2 (y1 y2))))) y0.
Definition term356 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term428 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term362 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) := fun y0 : real => (((~ (y0 = x0)) \/ (((x2 y0) = x0) \/ (@IN real (x2 y0) x1))) /\ ((~ (@IN real y0 x1)) \/ (((x2 y0) = x0) \/ (@IN real (x2 y0) x1)))) /\ (((~ (y0 = x0)) \/ (~ (real_le y0 (x2 y0)))) /\ ((~ (@IN real y0 x1)) \/ (~ (real_le y0 (x2 y0))))).
Definition term285 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ (((y2 = x0) \/ (@IN real y2 x1)) /\ (~ (real_le y1 y2)))) x2 y0.
Definition term131 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term125 := ~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3)).
Definition term87 (x0 : real) (x1 : real) (x2 : real -> Prop) := (x1 = x0) \/ (@IN real x1 x2).
Definition term373 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := (~ (x2 = x0)) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3)).
Definition term263 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0))) x3.
Definition term67 := fun y0 : real => forall y1 : real -> Prop, (((fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) y1) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) (@INSERT real y0 y1).
Definition term162 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term320 (x0 : real) (x1 : real) (x2 : real -> Prop) := (((forall y0 : real, ~ (@IN real y0 x2)) \/ ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((~ (y2 = x1)) /\ (~ (@IN real y2 x2))) \/ ((((y1 y2) = x1) \/ (@IN real (y1 y2) x2)) /\ (~ (real_le y2 (y1 y2))))) y0).
Definition term163 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => @IN real y1 x0) y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term383 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term390 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (@IN real (x0 x1) x2) -> ~ (@IN real (x0 x1) x2).
Definition term379 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le x2 x3) = (real_le x0 x1)) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term289 (x0 : real) (x1 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1)))).
Definition term288 (x0 : real) (x1 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ (((y3 = x0) \/ (@IN real y3 x1)) /\ (~ (real_le y2 y3)))) y0 y1).
Definition term432 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term404 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ~ ((~ (x2 = x0)) \/ (@IN real (x1 x2) x3)).
Definition term371 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le x1 y0)) x2.
Definition term190 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0)).
Definition term503 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) (x3 : real) := (@IN real (x1 x2) x0) \/ ((~ (x2 = x3)) \/ ((x1 x2) = x3)).
Definition term202 (x0 : real) (x1 : real -> Prop) := forall y0 : real, ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (exists y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1))).
Definition term474 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := @eq Prop (((x1 x2) = x0) \/ ((@IN real (x1 x2) x3) \/ (~ (@IN real x2 x3)))).
Definition term355 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) (x3 : real) := ((~ (x3 = x0)) \/ (~ (real_le x3 (x2 x3)))) /\ ((~ (@IN real x3 x1)) \/ (~ (real_le x3 (x2 x3)))).
Definition term224 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term549 (x0 : real) (x1 : real -> real) (x2 : real) := ((x1 x0) = x2) /\ (((x1 x2) = (x1 x2)) /\ (real_le (x1 x0) (x1 x2))).
Definition term426 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term170 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)).
Definition term154 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term173 (x0 : real -> Prop) := or (forall y0 : real, ~ (@IN real y0 x0)).
Definition term79 := (((~ ((@EMPTY real) = (@EMPTY real))) -> exists y0 : real, (@IN real y0 (@EMPTY real)) /\ (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1)) /\ (forall y0 : real, forall y1 : real -> Prop, (((~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (~ ((@INSERT real y0 y1) = (@EMPTY real))) -> exists y2 : real, (@IN real y2 (@INSERT real y0 y1)) /\ (forall y3 : real, (@IN real y3 (@INSERT real y0 y1)) -> real_le y2 y3))) -> forall y0 : real -> Prop, (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2).
Definition term191 (x0 : real) (x1 : real) (x2 : real -> Prop) := or (~ ((x1 = x0) \/ (@IN real x1 x2))).
Definition term367 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ~ (@IN real y0 x0)) x1.
Definition term402 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term233 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)))).
Definition term232 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2))) y0)).
Definition term258 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term176 (x0 : real -> Prop) := and ((forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)))).
Definition term342 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_le x1 x0) /\ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term396 (x0 : real -> real) (x1 : real) (x2 : real) := or ((x0 x1) = x2).
Definition term223 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term332 (x0 : real) (x1 : real -> Prop) := fun y0 : real => exists y1 : real -> real, (((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y0 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y0 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) /\ (forall y2 : real, ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ ((((y1 y2) = x0) \/ (@IN real (y1 y2) x1)) /\ (~ (real_le y2 (y1 y2))))).
Definition term221 := fun y0 : real => exists y1 : real -> Prop, (((forall y2 : real, ~ (@IN real y2 y1)) \/ (exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y2 y3)))) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) /\ (forall y2 : real, ((~ (y2 = y0)) /\ (~ (@IN real y2 y1))) \/ (exists y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) /\ (~ (real_le y2 y3)))).
Definition term422 (x0 : real -> real) (x1 : real) := real_le (x0 x1) (x0 x1).
Definition term242 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term177 (x0 : real) (x1 : real -> Prop) := ((forall y0 : real, ~ (@IN real y0 x1)) \/ (exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term445 (x0 : real -> real) (x1 : real) := ((x0 x1) = (x0 x1)) /\ (real_le (x0 x1) (x0 x1)).
Definition term219 (x0 : real) := ~ ((fun y0 : real => forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3)) x0).
Definition term273 (x0 : real) (x1 : real -> Prop) := fun y0 : real => exists y1 : real, ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1))).
Definition term448 (x0 : real -> real) (x1 : real) := real_le x1 (x0 x1).
Definition term301 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, (fun y1 : real => ((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) y0) /\ (exists y0 : real -> real, forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ ((((y0 y1) = x0) \/ (@IN real (y0 y1) x1)) /\ (~ (real_le y1 (y0 y1))))).
Definition term506 (x0 : real -> real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x2)) \/ ((x0 x1) = x2)).
Definition term156 (x0 : real -> Prop) := ~ (ex x0).
Definition term235 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, ~ (@IN real y0 x0)) \/ ((@IN real x1 x0) /\ (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le x1 y0))).
Definition term90 (x0 : real) (x1 : real) (x2 : real -> Prop) := imp (@IN real x0 (@INSERT real x1 x2)).
Definition term543 (x0 : real) (x1 : real -> real) (x2 : real) := ~ (real_le (x1 x0) (x1 x2)).
Definition term279 (x0 : real) (x1 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ (((y3 = x0) \/ (@IN real y3 x1)) /\ (~ (real_le y2 y3)))) y0 y1.
Definition term277 (x0 : type1626) := forall y0 : real, exists y1 : real, x0 y0 y1.
Definition term274 (x0 : real) (x1 : real -> Prop) := forall y0 : real, exists y1 : real, ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1))).
Definition term152 (x0 : real) (x1 : real -> Prop) := and (@IN real x0 x1).
Definition term150 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le x1 y0.
Definition term128 := (((~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term505 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := (~ ((~ (x2 = x0)) \/ ((x1 x2) = x0))) -> @IN real (x1 x2) x3.
Definition term37 (x0 : real -> Prop) := ~ (x0 = (@EMPTY real)).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := ~ (x0 = (@EMPTY a0)).
Definition term347 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term145 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term141 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term329 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real -> real => (((forall y1 : real, ~ (@IN real y1 x2)) \/ ((@IN real x0 x2) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le x0 y1)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ ((fun y1 : real -> real => forall y2 : real, ((~ (y2 = x1)) /\ (~ (@IN real y2 x2))) \/ ((((y1 y2) = x1) \/ (@IN real (y1 y2) x2)) /\ (~ (real_le y2 (y1 y2))))) y0).
Definition term22 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, ~ ((@INSERT a0 x0 y0) = (@EMPTY a0)).
Definition term361 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) (x3 : real) := (((~ (x3 = x0)) \/ (((x2 x3) = x0) \/ (@IN real (x2 x3) x1))) /\ ((~ (@IN real x3 x1)) \/ (((x2 x3) = x0) \/ (@IN real (x2 x3) x1)))) /\ (((~ (x3 = x0)) \/ (~ (real_le x3 (x2 x3)))) /\ ((~ (@IN real x3 x1)) \/ (~ (real_le x3 (x2 x3))))).
Definition term183 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term103 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1).
Definition term102 (x0 : real) (x1 : real -> Prop) := exists y0 : real, (@IN real y0 (@INSERT real x0 x1)) /\ (forall y1 : real, (@IN real y1 (@INSERT real x0 x1)) -> real_le y0 y1).
Definition term366 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) (x3 : real) := (fun y0 : real => (((~ (y0 = x0)) \/ (((x2 y0) = x0) \/ (@IN real (x2 y0) x1))) /\ ((~ (@IN real y0 x1)) \/ (((x2 y0) = x0) \/ (@IN real (x2 y0) x1)))) /\ (((~ (y0 = x0)) \/ (~ (real_le y0 (x2 y0)))) /\ ((~ (@IN real y0 x1)) \/ (~ (real_le y0 (x2 y0)))))) x3.
Definition term199 (x0 : real) (x1 : real -> Prop) (x2 : real) := ~ ((fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1)) x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term364 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term466 (x0 : real -> real) (x1 : real) := (real_le x1 (x0 x1)) -> ~ (real_le x1 (x0 x1)).
Definition term84 (x0 : real) (x1 : real -> Prop) := ~ ((@INSERT real x0 x1) = (@EMPTY real)).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((@INSERT a0 x0 x1) = (@EMPTY a0)).
Definition term464 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term519 (x0 : real -> Prop) (x1 : real) (x2 : real -> real) (x3 : real) := (@IN real (x2 x3) x0) -> real_le x1 (x2 x3).
Definition term225 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term459 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (~ (real_le x1 (x0 x1))) \/ (~ (@IN real x1 x2)).
Definition term62 (x0 : real) (x1 : real -> Prop) := (((~ (x1 = (@EMPTY real))) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) -> (~ ((@INSERT real x0 x1) = (@EMPTY real))) -> exists y0 : real, (@IN real y0 (@INSERT real x0 x1)) /\ (forall y1 : real, (@IN real y1 (@INSERT real x0 x1)) -> real_le y0 y1).
Definition term271 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ (((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0))).
Definition term115 (x0 : real -> Prop) := and ((exists y0 : real, @IN real y0 x0) -> exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1)).
Definition term405 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := (~ (~ (x2 = x0))) /\ (~ (@IN real (x1 x2) x3)).
Definition term435 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term501 (x0 : real -> real) (x1 : real) (x2 : real) := ((x0 x1) = x2) \/ (~ (x1 = x2)).
Definition term43 (x0 : type1022) := ((x0 (@EMPTY real)) /\ (forall y0 : real, forall y1 : real -> Prop, ((x0 y1) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> x0 (@INSERT real y0 y1))) -> forall y0 : real -> Prop, (@FINITE real y0) -> x0 y0.
Definition term28 (a0 : Type') (x0 : type686 a0) := ((x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term151 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le x1 y0.
Definition term462 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term212 (x0 : real) (x1 : real -> Prop) := (fun y0 : real -> Prop => (((exists y1 : real, @IN real y1 y0) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> exists y1 : real, ((y1 = x0) \/ (@IN real y1 y0)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) -> real_le y1 y2)) x1.
Definition term326 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((((forall y0 : real, ~ (@IN real y0 x2)) \/ ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ (exists y0 : real -> real, forall y1 : real, ((~ (y1 = x1)) /\ (~ (@IN real y1 x2))) \/ ((((y0 y1) = x1) \/ (@IN real (y0 y1) x2)) /\ (~ (real_le y1 (y0 y1)))))).
Definition term325 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((((forall y0 : real, ~ (@IN real y0 x2)) \/ ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((~ (y2 = x1)) /\ (~ (@IN real y2 x2))) \/ ((((y1 y2) = x1) \/ (@IN real (y1 y2) x2)) /\ (~ (real_le y2 (y1 y2))))) y0)).
Definition term341 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term281 (x0 : real) (x1 : real -> Prop) := fun y0 : real => fun y1 : real => ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1))).
Definition term187 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := ~ ((fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) -> real_le x2 y0) x3).
Definition term415 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := ((x2 = x2) /\ (~ (@IN real (x1 x2) x0))) -> (x1 x2) = x2.
Definition term71 := ((fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) (@EMPTY real)) /\ (forall y0 : real, forall y1 : real -> Prop, (((fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) y1) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) (@INSERT real y0 y1)).
Definition term124 := (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> False.
Definition term444 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ ((x1 = x3) /\ (real_le x0 x1))) -> real_le x2 x3.
Definition term57 (x0 : real) (x1 : real -> Prop) := imp (((fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) x1) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))).
Definition term455 (x0 : real -> real) (x1 : real) := (x1 = x1) /\ (real_le x1 (x0 x1)).
Definition term530 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ ((~ (real_le x1 x0)) \/ (real_le x1 x2)).
Definition term447 (x0 : real -> real) (x1 : real) := (((x0 x1) = x1) /\ (((x0 x1) = (x0 x1)) /\ (real_le (x0 x1) (x0 x1)))) -> real_le x1 (x0 x1).
Definition term139 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term550 (x0 : real) (x1 : real -> real) (x2 : real) := (((x1 x0) = x2) /\ (((x1 x2) = (x1 x2)) /\ (real_le (x1 x0) (x1 x2)))) -> real_le x2 (x1 x2).
Definition term496 (x0 : real -> real) (x1 : real) := (~ (real_le x1 (x0 x1))) /\ (real_le (x0 x1) (x0 x1)).
Definition term411 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := imp (~ ((~ (x2 = x0)) \/ (@IN real (x1 x2) x3))).
Definition term541 (x0 : real) (x1 : real -> real) (x2 : real) := (real_le x2 (x1 x0)) /\ (~ (real_le x2 (x1 x2))).
Definition term256 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((forall y0 : real, ~ (@IN real y0 x2)) \/ ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2)).
Definition term52 (x0 : real -> Prop) := and ((fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) x0).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, (~ (y0 = (@EMPTY a0))) = (exists y1 : a0, @IN a0 y1 y0).
Definition term508 (x0 : real -> real) (x1 : real) (x2 : real) := (x1 = x2) /\ (~ ((x0 x1) = x2)).
Definition term423 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term309 (x0 : real) (x1 : real -> Prop) (x2 : real) := and ((fun y0 : real => ((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) x2).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0))) x2.
Definition term291 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) (x3 : real) := (fun y0 : real => ((~ (x3 = x0)) /\ (~ (@IN real x3 x1))) \/ (((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x3 y0)))) (x2 x3).
Definition term418 (x0 : real -> real) (x1 : real) := (~ ((x0 x1) = (x0 x1))) -> (x0 x1) = (x0 x1).
Definition term454 (x0 : real) (x1 : real -> real) (x2 : real) := (x2 = x0) /\ (real_le x2 (x1 x2)).
Definition term471 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (@IN real (x0 x1) x2) \/ (~ (@IN real x1 x2)).
Definition term207 (x0 : real) (x1 : real -> Prop) := ~ ((((exists y0 : real, @IN real y0 x1) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) -> exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1)).
Definition term85 (x0 : real) (x1 : real -> Prop) := imp (~ ((@INSERT real x0 x1) = (@EMPTY real))).
Definition term129 := (((~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> ((~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term116 (x0 : real) (x1 : real -> Prop) := ((exists y0 : real, @IN real y0 x1) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term525 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term46 := (fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) (@EMPTY real).
Definition term429 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term33 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term440 (x0 : real) (x1 : real) (x2 : real) := (x2 = x0) /\ (real_le x1 x2).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term369 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1)) x1.
Definition term397 (x0 : real -> real) (x1 : real -> Prop) (x2 : real) (x3 : real) := ((x0 x2) = x3) \/ ((@IN real (x0 x2) x1) \/ (~ (x2 = x3))).
Definition term535 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term478 (x0 : real) (x1 : real -> Prop) := and (~ (~ (@IN real x0 x1))).
Definition term408 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term161 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => @IN real y0 x0) x1).
Definition term26 (a0 : Type') := forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term167 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le x1 y0).
Definition term80 := ~ ((@EMPTY real) = (@EMPTY real)).
Definition term345 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term120 (x0 : real) := forall y0 : real -> Prop, (((exists y1 : real, @IN real y1 y0) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> exists y1 : real, ((y1 = x0) \/ (@IN real y1 y0)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) -> real_le y1 y2).
Definition term107 (x0 : real) := forall y0 : real -> Prop, (((~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> exists y1 : real, ((y1 = x0) \/ (@IN real y1 y0)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) -> real_le y1 y2).
Definition term41 := forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((@INSERT a0 x0 x1) = (@EMPTY a0))) -> ((@INSERT a0 x0 x1) = (@EMPTY a0)) = False.
Definition term378 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term524 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ (~ (real_le x1 x2)).
Definition term358 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ((~ (x2 = x0)) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3))) /\ ((~ (@IN real x2 x3)) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3))).
Definition term484 (x0 : real -> real) (x1 : real) (x2 : real) := ~ ((x0 x1) = x2).
Definition term252 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, (forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))).
Definition term251 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => (forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) y0) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))).
Definition term236 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, ~ (@IN real y1 x0)) \/ ((fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2))) y0).
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0, @IN a0 y1 y0) = (~ (y0 = (@EMPTY a0))).
Definition term94 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => (@IN real y0 (@INSERT real x0 x1)) -> real_le x2 y0.
Definition term376 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (~ (@IN real x2 x0)) \/ (~ (real_le x2 (x1 x2))).
Definition term372 (x0 : real) (x1 : real -> real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_le x2 (x1 x2))).
Definition term485 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x1 = x0)) \/ ((real_le x3 x0) \/ (~ (real_le x2 x1))))) -> ~ (x2 = x3).
Definition term42 := forall y0 : real -> Prop, (@FINITE real y0) -> (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2).
Definition term226 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term243 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term60 (x0 : real) (x1 : real -> Prop) := (~ ((@INSERT real x0 x1) = (@EMPTY real))) -> exists y0 : real, (@IN real y0 (@INSERT real x0 x1)) /\ (forall y1 : real, (@IN real y1 (@INSERT real x0 x1)) -> real_le y0 y1).
Definition term192 (x0 : real) (x1 : real) (x2 : real -> Prop) := or ((~ (x1 = x0)) /\ (~ (@IN real x1 x2))).
Definition term118 (x0 : real) (x1 : real -> Prop) := (((exists y0 : real, @IN real y0 x1) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) -> exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1).
Definition term105 (x0 : real) (x1 : real -> Prop) := (((~ (x1 = (@EMPTY real))) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) -> exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1).
Definition term27 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) x0.
Definition term313 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => ((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) y0) /\ (exists y1 : real -> real, forall y2 : real, ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ ((((y1 y2) = x0) \/ (@IN real (y1 y2) x1)) /\ (~ (real_le y2 (y1 y2))))).
Definition term312 (x0 : real) (x1 : real) (x2 : real -> Prop) := (((forall y0 : real, ~ (@IN real y0 x2)) \/ ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ (exists y0 : real -> real, forall y1 : real, ((~ (y1 = x1)) /\ (~ (@IN real y1 x2))) \/ ((((y0 y1) = x1) \/ (@IN real (y0 y1) x2)) /\ (~ (real_le y1 (y0 y1))))).
Definition term77 := fun y0 : real -> Prop => (@FINITE real y0) -> (fun y1 : real -> Prop => (~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) y0.
Definition term349 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term147 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term359 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := and (((~ (x2 = x0)) /\ (~ (@IN real x2 x3))) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3))).
Definition term298 (x0 : real) (x1 : real -> Prop) := fun y0 : real -> real => forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ ((((y0 y1) = x0) \/ (@IN real (y0 y1) x1)) /\ (~ (real_le y1 (y0 y1)))).
Definition term297 (x0 : real) (x1 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ (((y3 = x0) \/ (@IN real y3 x1)) /\ (~ (real_le y2 y3)))) y1 (y0 y1).
Definition term282 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => fun y1 : real => ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1)))) x2.
Definition term234 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, ~ (@IN real y0 x0)) \/ ((fun y0 : real => (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1))) x1).
Definition term178 (x0 : real) (x1 : real) (x2 : real -> Prop) := ~ ((x1 = x0) \/ (@IN real x1 x2)).
Definition term158 (x0 : real -> Prop) := ~ (exists y0 : real, @IN real y0 x0).
Definition term352 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ((x1 x2) = x0) \/ (@IN real (x1 x2) x3).
Definition term86 (x0 : real) (x1 : real) (x2 : real -> Prop) := @IN real x0 (@INSERT real x1 x2).
Definition term290 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) (x3 : real) := (fun y0 : real => fun y1 : real => ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1)))) x3 (x2 x3).
Definition term30 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term545 (x0 : real) (x1 : real -> real) (x2 : real) := real_le (x1 x0) (x1 x2).
Definition term375 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term548 (x0 : real) (x1 : real -> real) (x2 : real) := ((x1 x2) = (x1 x2)) /\ (real_le (x1 x0) (x1 x2)).
Definition term164 (x0 : real -> Prop) := fun y0 : real => ~ (@IN real y0 x0).
Definition term283 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (fun y0 : real => fun y1 : real => ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1)))) x2 x3.
Definition term434 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term168 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le x1 y0).
Definition term437 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x2 = x0)) \/ (~ (real_le x1 x2))).
Definition term144 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term97 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) -> real_le x2 y0.
Definition term96 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, (@IN real y0 (@INSERT real x0 x1)) -> real_le x2 y0.
Definition term111 (x0 : real -> Prop) := exists y0 : real, @IN real y0 x0.
Definition term431 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))))).
Definition term475 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) (x3 : real) := (~ ((~ (@IN real x2 x0)) \/ (@IN real (x1 x2) x0))) -> (x1 x2) = x3.
Definition term401 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) (x3 : real) := (~ ((~ (x2 = x3)) \/ (@IN real (x1 x2) x0))) -> (x1 x2) = x3.
Definition term483 (x0 : real -> real) (x1 : real) (x2 : real) := (~ ((x0 x1) = x2)) -> (x0 x1) = x2.
Definition term395 (x0 : real -> real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (@IN real (x0 x2) x1) \/ (~ (x2 = x3)).
Definition term417 (x0 : real -> real) (x1 : real) := ~ ((x0 x1) = x1).
Definition term306 (x0 : real) (x1 : real -> Prop) := and (exists y0 : real, (fun y1 : real => ((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) y0).
Definition term250 (x0 : real -> Prop) := and (exists y0 : real, (fun y1 : real => (forall y2 : real, ~ (@IN real y2 x0)) \/ ((@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)))) y0).
Definition term465 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@IN real x2 x0) -> ~ (real_le x2 (x1 x2)).
Definition term304 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => ((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) y0.
Definition term509 (x0 : real -> real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x2)) \/ ((x0 x1) = x2))).
Definition term480 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := imp (~ ((~ (@IN real x1 x2)) \/ (@IN real (x0 x1) x2))).
Definition term421 (x0 : real -> real) (x1 : real) := (real_le (x0 x1) (x0 x1)) -> ~ (real_le (x0 x1) (x0 x1)).
Definition term31 (a0 : Type') (x0 : type686 a0) := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term513 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := ((x1 = x1) /\ (~ ((x0 x1) = x1))) -> @IN real (x0 x1) x2.
Definition term409 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term394 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := (~ (x2 = x0)) \/ (@IN real (x1 x2) x3).
Definition term135 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term536 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term456 (x0 : real -> real) (x1 : real) := ((x1 = x1) /\ (real_le x1 (x0 x1))) -> False.
Definition term453 (x0 : real) (x1 : real -> real) (x2 : real) := ((x2 = x0) /\ (real_le x2 (x1 x2))) -> False.
Definition term293 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((~ (y1 = x0)) /\ (~ (@IN real y1 x1))) \/ (((y2 = x0) \/ (@IN real y2 x1)) /\ (~ (real_le y1 y2)))) y0 (x2 y0).
Definition term382 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term387 (x0 : real) := ~ (x0 = x0).
Definition term436 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term302 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((fun y1 : real => ((forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) y0) /\ (exists y1 : real -> real, forall y2 : real, ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ ((((y1 y2) = x0) \/ (@IN real (y1 y2) x1)) /\ (~ (real_le y2 (y1 y2))))).
Definition term315 (x0 : real) (x1 : real -> Prop) := exists y0 : real, (((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) /\ (exists y1 : real -> real, forall y2 : real, ((~ (y2 = x0)) /\ (~ (@IN real y2 x1))) \/ ((((y1 y2) = x0) \/ (@IN real (y1 y2) x1)) /\ (~ (real_le y2 (y1 y2))))).
Definition term237 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, ~ (@IN real y1 x0)) \/ ((@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1))).
Definition term414 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (x1 = x1) /\ (~ (@IN real (x0 x1) x2)).
Definition term344 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term363 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) := forall y0 : real, (((~ (y0 = x0)) \/ (((x2 y0) = x0) \/ (@IN real (x2 y0) x1))) /\ ((~ (@IN real y0 x1)) \/ (((x2 y0) = x0) \/ (@IN real (x2 y0) x1)))) /\ (((~ (y0 = x0)) \/ (~ (real_le y0 (x2 y0)))) /\ ((~ (@IN real y0 x1)) \/ (~ (real_le y0 (x2 y0))))).
Definition term446 (x0 : real -> real) (x1 : real) := ((x0 x1) = x1) /\ (((x0 x1) = (x0 x1)) /\ (real_le (x0 x1) (x0 x1))).
Definition term489 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (real_le x0 x1)) /\ (~ (~ (real_le x2 x3))).
Definition term197 (x0 : real) (x1 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 x1)) -> real_le y1 y2)) y0).
Definition term159 (x0 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => @IN real y1 x0) y0).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term294 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) := fun y0 : real => ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ ((((x2 y0) = x0) \/ (@IN real (x2 y0) x1)) /\ (~ (real_le y0 (x2 y0)))).
Definition term336 := fun y0 : real => exists y1 : real -> Prop, exists y2 : real, exists y3 : real -> real, (((forall y4 : real, ~ (@IN real y4 y1)) \/ ((@IN real y2 y1) /\ (forall y4 : real, (~ (@IN real y4 y1)) \/ (real_le y2 y4)))) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) /\ (forall y4 : real, ((~ (y4 = y0)) /\ (~ (@IN real y4 y1))) \/ ((((y3 y4) = y0) \/ (@IN real (y3 y4) y1)) /\ (~ (real_le y4 (y3 y4))))).
Definition term194 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ (exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0))).
Definition term458 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) -> @IN real x0 x1.
Definition term200 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) /\ (forall y2 : real, ((y2 = x0) \/ (@IN real y2 x1)) -> real_le y1 y2)) y0).
Definition term188 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => ~ ((fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) -> real_le x2 y1) y0).
Definition term381 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term310 (x0 : real) (x1 : real) (x2 : real -> Prop) := and (((forall y0 : real, ~ (@IN real y0 x2)) \/ ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))).
Definition term54 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) /\ (@FINITE real x1).
Definition term75 (x0 : real -> Prop) := imp (@FINITE real x0).
Definition term542 (x0 : real) (x1 : real -> real) (x2 : real) := ((real_le x2 (x1 x0)) /\ (~ (real_le x2 (x1 x2)))) -> ~ (real_le (x1 x0) (x1 x2)).
Definition term155 (x0 : real -> Prop) := fun y0 : real => @IN real y0 x0.
Definition term204 (x0 : real) (x1 : real -> Prop) := and (((forall y0 : real, ~ (@IN real y0 x1)) \/ (exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))).
Definition term203 (x0 : real) (x1 : real -> Prop) := and (((exists y0 : real, @IN real y0 x1) -> exists y0 : real, (@IN real y0 x1) /\ (forall y1 : real, (@IN real y1 x1) -> real_le y0 y1)) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))).
Definition term441 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3)).
Definition term507 (x0 : real -> real) (x1 : real) (x2 : real) := (~ (~ (x1 = x2))) /\ (~ ((x0 x1) = x2)).
Definition term240 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, (forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term149 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) -> real_le x1 x2.
Definition term498 (x0 : real -> real) (x1 : real) := (((x0 x1) = (x0 x1)) /\ ((~ (real_le x1 (x0 x1))) /\ (real_le (x0 x1) (x0 x1)))) -> ~ ((x0 x1) = x1).
Definition term354 (x0 : real) (x1 : real -> Prop) (x2 : real -> real) (x3 : real) := ((~ (x3 = x0)) /\ (~ (@IN real x3 x1))) \/ (~ (real_le x3 (x2 x3))).
Definition term171 (x0 : real -> Prop) := exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)).
Definition term38 (x0 : real -> Prop) := exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term516 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((~ (@IN real x2 x0)) \/ (real_le x1 x2)).
Definition term209 (x0 : type1022) := exists y0 : real -> Prop, ~ (x0 y0).
Definition term452 (x0 : real) (x1 : real -> real) (x2 : real) := ~ ((x2 = x0) /\ (real_le x2 (x1 x2))).
Definition term193 (x0 : real) (x1 : real -> Prop) (x2 : real) := (~ ((x2 = x0) \/ (@IN real x2 x1))) \/ (~ (forall y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) -> real_le x2 y0)).
Definition term321 (x0 : real) (x1 : real) (x2 : real -> Prop) := exists y0 : real -> real, (((forall y1 : real, ~ (@IN real y1 x2)) \/ ((@IN real x0 x2) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le x0 y1)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ ((fun y1 : real -> real => forall y2 : real, ((~ (y2 = x1)) /\ (~ (@IN real y2 x2))) \/ ((((y1 y2) = x1) \/ (@IN real (y1 y2) x2)) /\ (~ (real_le y2 (y1 y2))))) y0).
Definition term95 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) -> real_le x2 y0.
Definition term495 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x1 = x0) /\ ((~ (real_le x3 x0)) /\ (real_le x2 x1))) -> ~ (x2 = x3).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term201 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((~ (y0 = x0)) /\ (~ (@IN real y0 x1))) \/ (exists y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le y0 y1))).
Definition term143 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term547 (x0 : real) (x1 : real -> real) (x2 : real) := (~ (real_le (x1 x0) (x1 x2))) -> real_le (x1 x0) (x1 x2).
Definition term546 (x0 : real) (x1 : real -> real) (x2 : real) := (~ (real_le (x1 x2) (x1 x0))) -> real_le (x1 x0) (x1 x2).
Definition term47 := (~ ((@EMPTY real) = (@EMPTY real))) -> exists y0 : real, (@IN real y0 (@EMPTY real)) /\ (forall y1 : real, (@IN real y1 (@EMPTY real)) -> real_le y0 y1).
Definition term68 := fun y0 : real => forall y1 : real -> Prop, (((~ (y1 = (@EMPTY real))) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (~ ((@INSERT real y0 y1) = (@EMPTY real))) -> exists y2 : real, (@IN real y2 (@INSERT real y0 y1)) /\ (forall y3 : real, (@IN real y3 (@INSERT real y0 y1)) -> real_le y2 y3).
Definition term32 (a0 : Type') := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term473 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((~ (@IN real x2 x3)) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3))).
Definition term398 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((~ (x2 = x0)) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3))).
Definition term64 (x0 : real) := fun y0 : real -> Prop => (((~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) -> (~ ((@INSERT real x0 y0) = (@EMPTY real))) -> exists y1 : real, (@IN real y1 (@INSERT real x0 y0)) /\ (forall y2 : real, (@IN real y2 (@INSERT real x0 y0)) -> real_le y1 y2).
Definition term172 (x0 : real -> Prop) := or (~ (exists y0 : real, @IN real y0 x0)).
Definition term526 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ ((real_le x0 x2) \/ (~ (real_le x1 x2))).
Definition term241 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term268 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ ((fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0))) x3).
Definition term269 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ (((x3 = x0) \/ (@IN real x3 x1)) /\ (~ (real_le x2 x3))).
Definition term245 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, (fun y1 : real => (forall y2 : real, ~ (@IN real y2 x1)) \/ ((@IN real y1 x1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)))) y0) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term491 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (real_le x0 x1)) /\ (real_le x2 x3).
Definition term327 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real -> real) := (((forall y0 : real, ~ (@IN real y0 x2)) \/ ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ ((fun y0 : real -> real => forall y1 : real, ((~ (y1 = x1)) /\ (~ (@IN real y1 x2))) \/ ((((y0 y1) = x1) \/ (@IN real (y0 y1) x2)) /\ (~ (real_le y1 (y0 y1))))) x3).
Definition term10 (a0 : Type') := fun y0 : a0 -> Prop => (~ (y0 = (@EMPTY a0))) = (exists y1 : a0, @IN a0 y1 y0).
Definition term490 (x0 : real) (x1 : real) := and (~ (real_le x0 x1)).
Definition term407 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term189 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0)).
Definition term377 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := (~ (@IN real x2 x3)) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3)).
Definition term253 (x0 : real -> Prop) (x1 : real) := and ((fun y0 : real => (forall y1 : real, ~ (@IN real y1 x0)) \/ ((@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)))) x1).
Definition term357 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real -> Prop) := ((~ (x2 = x0)) /\ (~ (@IN real x2 x3))) \/ (((x1 x2) = x0) \/ (@IN real (x1 x2) x3)).
Definition term427 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term338 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term238 (x0 : real -> Prop) := exists y0 : real, (forall y1 : real, ~ (@IN real y1 x0)) \/ ((@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1))).
Definition term175 (x0 : real -> Prop) := (forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, @IN a0 y0 x0.
Definition term523 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ (real_le x1 x2).
Definition term276 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term29 (a0 : Type') (x0 : type686 a0) := (x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1)).
Definition term502 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := or (@IN real (x0 x1) x2).
Definition term45 := fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2).
Definition term15 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term114 (x0 : real -> Prop) := (exists y0 : real, @IN real y0 x0) -> exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term492 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) /\ ((~ (real_le x0 x1)) /\ (real_le x2 x3)).
Definition term51 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) -> exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term368 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2)) x0.
Definition term73 := imp (((fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) (@EMPTY real)) /\ (forall y0 : real, forall y1 : real -> Prop, (((fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) y1) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> (fun y2 : real -> Prop => (~ (y2 = (@EMPTY real))) -> exists y3 : real, (@IN real y3 y2) /\ (forall y4 : real, (@IN real y4 y2) -> real_le y3 y4)) (@INSERT real y0 y1))).
Definition term385 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3)))).
Definition term126 := (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term260 (x0 : real) (x1 : real -> Prop) := and (exists y0 : real, ((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))).
Definition term239 (x0 : real -> Prop) := and (exists y0 : real, (forall y1 : real, ~ (@IN real y1 x0)) \/ ((@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)))).
Definition term420 (x0 : real -> real) (x1 : real) := ~ (real_le (x0 x1) (x0 x1)).
Definition term36 (x0 : real -> Prop) := (@FINITE real x0) -> (~ (x0 = (@EMPTY real))) -> exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term527 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term81 := imp (~ ((@EMPTY real) = (@EMPTY real))).
Definition term424 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term468 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (~ (real_le x1 (x0 x1))) -> ~ (@IN real (x0 x1) x2).
Definition term330 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real -> real => (((forall y1 : real, ~ (@IN real y1 x2)) \/ ((@IN real x0 x2) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le x0 y1)))) /\ ((~ (@IN real x1 x2)) /\ (@FINITE real x2))) /\ (forall y1 : real, ((~ (y1 = x1)) /\ (~ (@IN real y1 x2))) \/ ((((y0 y1) = x1) \/ (@IN real (y0 y1) x2)) /\ (~ (real_le y1 (y0 y1))))).
Definition term215 (x0 : real) := fun y0 : real -> Prop => (((forall y1 : real, ~ (@IN real y1 y0)) \/ (exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y1 y2)))) /\ ((~ (@IN real x0 y0)) /\ (@FINITE real y0))) /\ (forall y1 : real, ((~ (y1 = x0)) /\ (~ (@IN real y1 y0))) \/ (exists y2 : real, ((y2 = x0) \/ (@IN real y2 y0)) /\ (~ (real_le y1 y2)))).
Definition term460 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := @eq Prop ((~ (@IN real x2 x0)) \/ (~ (real_le x2 (x1 x2)))).
Definition term520 (x0 : real) (x1 : real -> real) (x2 : real) := real_le x0 (x1 x2).
Definition term61 (x0 : real) (x1 : real -> Prop) := (((fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) x1) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1))) -> (fun y0 : real -> Prop => (~ (y0 = (@EMPTY real))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2)) (@INSERT real x0 x1).
Definition term259 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((forall y1 : real, ~ (@IN real y1 x1)) \/ ((@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)))) /\ ((~ (@IN real x0 x1)) /\ (@FINITE real x1)).
Definition term272 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real, ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ (((y0 = x0) \/ (@IN real y0 x1)) /\ (~ (real_le x2 y0))).
Definition term365 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term136 := imp (~ (forall y0 : real, forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3))).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term392 (x0 : Prop) := x0 -> ~ x0.
Definition term218 (x0 : real) := (fun y0 : real => forall y1 : real -> Prop, (((exists y2 : real, @IN real y2 y1) -> exists y2 : real, (@IN real y2 y1) /\ (forall y3 : real, (@IN real y3 y1) -> real_le y2 y3)) /\ ((~ (@IN real y0 y1)) /\ (@FINITE real y1))) -> exists y2 : real, ((y2 = y0) \/ (@IN real y2 y1)) /\ (forall y3 : real, ((y3 = y0) \/ (@IN real y3 y1)) -> real_le y2 y3)) x0.
Definition term198 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1)) x2.
Definition term510 (x0 : real -> real) (x1 : real) (x2 : real) := imp ((x1 = x2) /\ (~ ((x0 x1) = x2))).
Definition term481 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := imp ((@IN real x1 x2) /\ (~ (@IN real (x0 x1) x2))).
Definition term380 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term346 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term227 (x0 : real -> Prop) := (forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2))) y0).
Definition term339 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_le x1 x2)).
Definition term534 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x1 x0))) /\ (~ (real_le x1 x2)).
Definition term196 (x0 : real) (x1 : real -> Prop) := ~ (exists y0 : real, ((y0 = x0) \/ (@IN real y0 x1)) /\ (forall y1 : real, ((y1 = x0) \/ (@IN real y1 x1)) -> real_le y0 y1)).
Definition term463 (x0 : real) (x1 : real -> Prop) := imp (~ (~ (@IN real x0 x1))).
Definition term270 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => ((~ (x2 = x0)) /\ (~ (@IN real x2 x1))) \/ ((fun y1 : real => ((y1 = x0) \/ (@IN real y1 x1)) /\ (~ (real_le x2 y1))) y0).
