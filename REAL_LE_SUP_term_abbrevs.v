Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term120 (x0 : real) (x1 : real) (x2 : real -> Prop) := (exists y0 : real, (fun y1 : real => (@IN real y1 x2) /\ ((real_le x1 y1) /\ (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 x0)))) y0) /\ (~ (real_le x1 (sup x2))).
Definition term645 (x0 : real) (x1 : real -> Prop) := (~ (~ (@IN real x0 x1))) /\ (~ (real_le x0 (sup x1))).
Definition term488 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))).
Definition term429 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0.
Definition term425 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0.
Definition term605 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1)) x2.
Definition term614 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term530 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (forall y0 : real, ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))).
Definition term193 (x0 : real -> Prop) := ((exists y0 : real, @IN real y0 x0) \/ (x0 = (@EMPTY real))) /\ ((forall y0 : real, ~ (@IN real y0 x0)) \/ (~ (x0 = (@EMPTY real)))).
Definition term205 (x0 : real -> Prop) := and ((fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) x0).
Definition term50 (x0 : real -> Prop) := @eq Prop (exists y0 : real, @IN real y0 x0).
Definition term528 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := or ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2)))).
Definition term466 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0).
Definition term394 (x0 : real -> real) (x1 : real -> Prop) := fun y0 : real => ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le (sup x1) y0).
Definition term304 (x0 : real -> Prop) := ~ ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term560 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (@IN real (x0 x1 x2) x1) \/ (real_le (sup x1) x2).
Definition term77 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (@IN real x1 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le y0 x3))).
Definition term63 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (@IN real x1 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le y0 x3)).
Definition term107 (x0 : type1022) := ~ (all x0).
Definition term84 (x0 : real -> Prop) := ~ (all x0).
Definition term708 := (~ False) -> False.
Definition term499 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)) x2.
Definition term430 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0.
Definition term426 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0.
Definition term474 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term440 := fun y0 : real -> Prop => exists y1 : real -> real, ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term22 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2).
Definition term572 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))) /\ (((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term518 (x0 : real -> Prop) (x1 : Prop) := forall y0 : real, (x0 y0) \/ x1.
Definition term236 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) \/ (x0 = (@EMPTY real)).
Definition term573 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := and ((((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) /\ ((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1)))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term161 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le x0 x1) /\ (real_le x1 x2))).
Definition term257 (x0 : type1023) (x1 : real -> Prop) := (@IN real (x0 x1) x1) \/ (x1 = (@EMPTY real)).
Definition term301 (x0 : real -> Prop) := or (x0 = (@EMPTY real)).
Definition term204 (x0 : real -> Prop) := (fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) x0.
Definition term503 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term502 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) y0) /\ (forall y0 : real, (fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0)).
Definition term437 (x0 : real -> Prop) := fun y0 : real -> real => ((fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0) \/ ((fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0).
Definition term670 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (real_le x2 (sup x3)) \/ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)))).
Definition term74 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term154 := exists y0 : real -> Prop, exists y1 : real, (exists y2 : real, exists y3 : real, (@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (~ (@IN real y4 y0)) \/ (real_le y4 y2)))) /\ (~ (real_le y1 (sup y0))).
Definition term481 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0.
Definition term365 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0.
Definition term124 (x0 : real) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((fun y0 : real => (@IN real y0 x3) /\ ((real_le x2 y0) /\ (forall y1 : real, (~ (@IN real y1 x3)) \/ (real_le y1 x0)))) x1) /\ (~ (real_le x2 (sup x3))).
Definition term622 (x0 : Prop) := ~ (~ x0).
Definition term130 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real, (@IN real y0 x1) /\ ((real_le x0 y0) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x2))).
Definition term19 := imp (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))).
Definition term610 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2)).
Definition term647 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) /\ (~ (real_le x0 (sup x1))).
Definition term463 := fun y0 : type1021 => forall y1 : real -> Prop, ((y1 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y0 y1 y2) y1) /\ (~ (real_le (y0 y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 (sup y1))) /\ (forall y2 : real, ((@IN real (y0 y1 y2) y1) /\ (~ (real_le (y0 y1 y2) y2))) \/ (real_le (sup y1) y2))).
Definition term26 := (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> ~ (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)).
Definition term109 := exists y0 : real -> Prop, ~ ((fun y1 : real -> Prop => forall y2 : real, forall y3 : real, forall y4 : real, ((@IN real y4 y1) /\ ((real_le y2 y4) /\ (forall y5 : real, (@IN real y5 y1) -> real_le y5 y3))) -> real_le y2 (sup y1)) y0).
Definition term59 (x0 : real) (x1 : real -> Prop) := real_le x0 (sup x1).
Definition term265 := and (exists y0 : type1023, forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))).
Definition term182 (x0 : real -> Prop) := ~ (~ (x0 = (@EMPTY real))).
Definition term570 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)))).
Definition term345 (x0 : real -> Prop) := (x0 = (@EMPTY real)) \/ (exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term617 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) \/ (~ (@IN real x0 x1)).
Definition term414 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ ((fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0).
Definition term551 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := @IN real (x0 x2 x1) x2.
Definition term562 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)).
Definition term208 := fun y0 : real -> Prop => ((fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0) /\ ((fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0).
Definition term681 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (~ (real_le (x0 x3 x1) x1))) /\ (~ (~ (@IN real x2 x3))).
Definition term314 (x0 : real -> Prop) := and (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))).
Definition term38 (x0 : real -> Prop) := and (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)).
Definition term470 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)).
Definition term661 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (real_le (x0 x3 x1) x1)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term262 := fun y0 : type1023 => forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y1 (y0 y1).
Definition term601 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0)) x2.
Definition term424 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) x1.
Definition term700 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x1))) /\ (~ (~ (real_le x1 x2))).
Definition term701 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term418 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term511 (x0 : type1021) (x1 : real -> Prop) := (fun y0 : Prop => y0 = (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)))) ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term24 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> ~ (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)).
Definition term356 (x0 : real -> Prop) := @eq Prop ((x0 = (@EMPTY real)) \/ (exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))).
Definition term355 (x0 : real -> Prop) := @eq Prop ((x0 = (@EMPTY real)) \/ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0)).
Definition term357 (x0 : real -> Prop) (x1 : real -> real) := (x0 = (@EMPTY real)) \/ ((fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) x1).
Definition term475 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term535 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := forall y0 : real, ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ ((fun y1 : real => ((~ (@IN real y1 x2)) \/ (real_le y1 (sup x2))) /\ (((@IN real (x1 x2 y1) x2) /\ (~ (real_le (x1 x2 y1) y1))) \/ (real_le (sup x2) y1))) y0).
Definition term281 := fun y0 : type1023 => ((fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0) /\ (forall y1 : real -> Prop, (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term20 := (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False.
Definition term417 (x0 : real -> Prop) := (exists y0 : real -> real, (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ (exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))).
Definition term41 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0.
Definition term555 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := or (((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 x2) x1)) /\ ((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 x2) x2)))).
Definition term498 (x0 : real -> Prop) := and (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) y0).
Definition term402 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term540 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := @eq Prop (((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (forall y0 : real, ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0)))).
Definition term539 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := @eq Prop (((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (forall y0 : real, (fun y1 : real => ((~ (@IN real y1 x2)) \/ (real_le y1 (sup x2))) /\ (((@IN real (x1 x2 y1) x2) /\ (~ (real_le (x1 x2 y1) y1))) \/ (real_le (sup x2) y1))) y0)).
Definition term29 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le y0 x1.
Definition term137 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, (fun y1 : real => exists y2 : real, (@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (~ (@IN real y3 x1)) \/ (real_le y3 y1)))) y0) /\ (~ (real_le x0 (sup x1))).
Definition term220 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term703 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term286 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term86 (x0 : real) (x1 : real) (x2 : real -> Prop) := ~ (forall y0 : real, ((@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (@IN real y1 x2) -> real_le y1 x0))) -> real_le x1 (sup x2)).
Definition term73 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x1 x0)) \/ (real_le x1 x2).
Definition term571 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) /\ ((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1)))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term311 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1).
Definition term585 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => ~ (@IN real y1 x0)) y0.
Definition term682 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ~ (~ (real_le (x0 x1 x2) x2)).
Definition term75 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term536 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))) x2.
Definition term407 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)) x1.
Definition term352 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) x1.
Definition term439 (x0 : real -> Prop) := exists y0 : real -> real, ((x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))).
Definition term117 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term596 (x0 : real -> Prop) := forall y0 : real, (~ (@IN real y0 x0)) \/ (~ (x0 = (@EMPTY real))).
Definition term316 (x0 : real -> Prop) := or (~ ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0))).
Definition term412 (x0 : real -> Prop) (x1 : real -> real) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ ((fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)) x1).
Definition term18 := forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1).
Definition term403 (x0 : Prop) (x1 : type1028) := x0 /\ (exists y0 : real -> real, x1 y0).
Definition term181 (x0 : real -> Prop) := forall y0 : real, ~ (@IN real y0 x0).
Definition term644 (x0 : real) (x1 : real -> Prop) := ~ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1))).
Definition term191 (x0 : real -> Prop) := and ((exists y0 : real, @IN real y0 x0) \/ (x0 = (@EMPTY real))).
Definition term408 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0.
Definition term353 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0.
Definition term457 (x0 : type1021) (x1 : real -> Prop) := ((x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term436 (x0 : real -> real) (x1 : real -> Prop) := ((x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0)))) \/ ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term319 (x0 : real -> Prop) := ((x0 = (@EMPTY real)) \/ (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)))) \/ ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0))).
Definition term471 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)).
Definition term341 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0)).
Definition term566 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)).
Definition term438 (x0 : real -> Prop) := fun y0 : real -> real => ((x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))).
Definition term620 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term668 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))))).
Definition term230 (x0 : real -> Prop) := @eq Prop ((exists y0 : real, @IN real y0 x0) \/ (x0 = (@EMPTY real))).
Definition term229 (x0 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => @IN real y1 x0) y0) \/ (x0 = (@EMPTY real))).
Definition term266 := (exists y0 : type1023, forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term632 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (@IN real (x0 x3 x1) x3) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term493 (x0 : type1021) (x1 : real -> Prop) := (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) y0) /\ (forall y0 : real, (fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0).
Definition term364 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ((fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0) \/ (real_le (sup x0) x1).
Definition term416 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)).
Definition term283 := exists y0 : type1023, (forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) /\ (forall y1 : real -> Prop, (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))).
Definition term387 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y0 y1.
Definition term332 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1.
Definition term476 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (forall y0 : real, x1 y0).
Definition term513 (x0 : type1021) (x1 : real -> Prop) := @eq Prop (((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))) = (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)))).
Definition term581 (x0 : type1021) := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0)))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))))) /\ (((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2)))) /\ ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))))).
Definition term549 (x0 : type1021) := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, ((y0 = (@EMPTY real)) \/ ((@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1)))) \/ (((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (((@IN real (x0 y0 y2) y0) /\ (~ (real_le (x0 y0 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term8 := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0).
Definition term659 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := real_le (x0 x1 x2) x2.
Definition term210 := @eq Prop (forall y0 : real -> Prop, ((exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) /\ ((forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))))).
Definition term567 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))).
Definition term222 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) \/ x1.
Definition term114 := exists y0 : real -> Prop, exists y1 : real, exists y2 : real, exists y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (~ (@IN real y4 y0)) \/ (real_le y4 y2)))) /\ (~ (real_le y1 (sup y0))).
Definition term190 (x0 : real -> Prop) := and ((exists y0 : real, @IN real y0 x0) \/ (~ (~ (x0 = (@EMPTY real))))).
Definition term401 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term185 (x0 : real -> Prop) := (~ (exists y0 : real, @IN real y0 x0)) \/ (~ (x0 = (@EMPTY real))).
Definition term224 (x0 : real -> Prop) := (exists y0 : real, (fun y1 : real => @IN real y1 x0) y0) \/ (x0 = (@EMPTY real)).
Definition term580 (x0 : type1021) := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0)))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))))) /\ (((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2)))) /\ ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))))).
Definition term548 (x0 : type1021) := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, ((y0 = (@EMPTY real)) \/ ((@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1)))) \/ (((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (((@IN real (x0 y0 y2) y0) /\ (~ (real_le (x0 y0 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term72 := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0).
Definition term113 := fun y0 : real -> Prop => exists y1 : real, exists y2 : real, exists y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (~ (@IN real y4 y0)) \/ (real_le y4 y2)))) /\ (~ (real_le y1 (sup y0))).
Definition term10 := ~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0)).
Definition term339 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0)).
Definition term608 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term261 (x0 : type1023) := forall y0 : real -> Prop, (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real)).
Definition term164 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term615 (x0 : Prop) := (~ x0) -> x0.
Definition term188 (x0 : real -> Prop) := (exists y0 : real, @IN real y0 x0) \/ (~ (~ (x0 = (@EMPTY real)))).
Definition term520 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0) \/ (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term349 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 \/ (x1 y0).
Definition term665 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ (@IN real x0 x2)) \/ ((real_le x0 (sup x2)) \/ (~ (real_le (x1 x2 x3) x3))).
Definition term609 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term360 (x0 : real -> Prop) := fun y0 : real -> real => (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term33 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0.
Definition term76 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (real_le x0 x1) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le y0 x3)).
Definition term61 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le y0 x3).
Definition term648 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) /\ ((@IN real x0 x1) /\ (~ (real_le x0 (sup x1)))).
Definition term44 (x0 : real -> Prop) := imp ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term641 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term626 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) -> ~ (x1 = (@EMPTY real)).
Definition term455 (x0 : type1021) (x1 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real -> real => ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2)))) x1 (x0 x1).
Definition term240 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term672 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)).
Definition term400 (x0 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)).
Definition term637 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (@IN real (x0 x3 x1) x3) \/ ((x3 = (@EMPTY real)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term96 (x0 : real) (x1 : real -> Prop) (x2 : real) := ~ ((fun y0 : real => forall y1 : real, ((@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (@IN real y2 x1) -> real_le y2 y0))) -> real_le x0 (sup x1)) x2).
Definition term67 (x0 : real) (x1 : real) (x2 : real -> Prop) := forall y0 : real, ((@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (@IN real y1 x2) -> real_le y1 x0))) -> real_le x1 (sup x2).
Definition term696 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2))).
Definition term462 := fun y0 : type1021 => forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y1 (y0 y1).
Definition term507 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((~ (@IN real x2 x1)) \/ (real_le x2 (sup x1))) /\ (((@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2))) \/ (real_le (sup x1) x2)).
Definition term495 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) x1.
Definition term366 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0.
Definition term129 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real, (fun y1 : real => (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 x2)))) y0.
Definition term23 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False.
Definition term579 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1)))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))))) /\ (((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1)))) /\ ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))))).
Definition term547 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term171 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term169 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term71 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, forall y2 : real, ((@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (@IN real y3 x0) -> real_le y3 y1))) -> real_le y0 (sup x0).
Definition term69 (x0 : real) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, ((@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (@IN real y2 x1) -> real_le y2 y0))) -> real_le x0 (sup x1).
Definition term58 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term56 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term308 (x0 : real -> Prop) (x1 : real) := or (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)).
Definition term697 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term464 := exists y0 : type1021, forall y1 : real -> Prop, ((y1 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y0 y1 y2) y1) /\ (~ (real_le (y0 y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 (sup y1))) /\ (forall y2 : real, ((@IN real (y0 y1 y2) y1) /\ (~ (real_le (y0 y1 y2) y2))) \/ (real_le (sup y1) y2))).
Definition term445 := exists y0 : type1021, forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y1 (y0 y1).
Definition term443 (x0 : type1017) := exists y0 : type1021, forall y1 : real -> Prop, x0 y1 (y0 y1).
Definition term399 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1).
Definition term380 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y1 (y0 y1).
Definition term344 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)).
Definition term325 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y1 (y0 y1).
Definition term323 (x0 : type1626) := exists y0 : real -> real, forall y1 : real, x0 y1 (y0 y1).
Definition term264 := exists y0 : type1023, forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real)).
Definition term245 := exists y0 : type1023, forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y1 (y0 y1).
Definition term243 (x0 : type1020) := exists y0 : type1023, forall y1 : real -> Prop, x0 y1 (y0 y1).
Definition term510 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)).
Definition term527 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := or ((fun y0 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) x2).
Definition term370 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1))) x2).
Definition term147 (x0 : real) (x1 : real -> Prop) := exists y0 : real, exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0))).
Definition term106 (x0 : real -> Prop) := exists y0 : real, exists y1 : real, exists y2 : real, ((@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y1)))) /\ (~ (real_le y0 (sup x0))).
Definition term99 (x0 : real) (x1 : real -> Prop) := exists y0 : real, exists y1 : real, ((@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) /\ (~ (real_le x0 (sup x1))).
Definition term173 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term490 (x0 : type1021) (x1 : real -> Prop) := or (forall y0 : real, (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))).
Definition term449 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => ((x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)))) x1.
Definition term515 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term367 (x0 : real -> Prop) (x1 : real) := or (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0).
Definition term228 (x0 : real -> Prop) := or (exists y0 : real, (fun y1 : real => @IN real y1 x0) y0).
Definition term485 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (x1 = (@EMPTY real)) \/ ((fun y0 : real => (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) x2).
Definition term433 (x0 : real -> Prop) (x1 : real -> real) := or ((fun y0 : real -> real => (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) x1).
Definition term654 (x0 : real) (x1 : real) (x2 : real -> Prop) := (real_le x1 x0) \/ (~ (@IN real x1 x2)).
Definition term521 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) x2.
Definition term613 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term393 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le (sup x0) y1)) y0 (x1 y0).
Definition term338 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) y0 (x1 y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term337 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@IN real (x1 x2) x0) /\ (~ (real_le (x1 x2) x2)).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term213 := forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term676 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))))) -> real_le x2 (sup x3).
Definition term248 (x0 : real -> Prop) (x1 : real) := (fun y0 : real -> Prop => fun y1 : real => (@IN real y1 y0) \/ (y0 = (@EMPTY real))) x0 x1.
Definition term232 (x0 : real) (x1 : real -> Prop) := or (@IN real x0 x1).
Definition term88 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (fun y0 : real => ((@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (@IN real y1 x2) -> real_le y1 x0))) -> real_le x1 (sup x2)) x3.
Definition term629 (x0 : real) (x1 : real -> Prop) := (real_le x0 (sup x1)) -> ~ (real_le x0 (sup x1)).
Definition term247 (x0 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real => (@IN real y1 y0) \/ (y0 = (@EMPTY real))) x0.
Definition term643 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) /\ (~ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1)))).
Definition term651 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := ((~ (x3 = (@EMPTY real))) /\ ((@IN real x0 x3) /\ (~ (real_le x0 (sup x3))))) -> @IN real (x1 x3 x2) x3.
Definition term404 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 /\ (x1 y0).
Definition term607 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (~ (x0 = (@EMPTY real)))) x1.
Definition term176 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => @IN real y0 x0) x1.
Definition term287 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 x1) y0).
Definition term101 (x0 : real -> Prop) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((@IN real y3 x0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 x0) -> real_le y4 y2))) -> real_le y1 (sup x0)) y0).
Definition term94 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (@IN real y3 x1) -> real_le y3 y1))) -> real_le x0 (sup x1)) y0).
Definition term87 (x0 : real) (x1 : real) (x2 : real -> Prop) := exists y0 : real, ~ ((fun y1 : real => ((@IN real y1 x2) /\ ((real_le x1 y1) /\ (forall y2 : real, (@IN real y2 x2) -> real_le y2 x0))) -> real_le x1 (sup x2)) y0).
Definition term522 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0.
Definition term496 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) y0.
Definition term689 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((~ (x3 = (@EMPTY real))) /\ ((real_le (x0 x3 x1) x1) /\ (@IN real x2 x3))) -> real_le x2 (sup x3).
Definition term606 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))) x0.
Definition term688 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := imp ((~ (x3 = (@EMPTY real))) /\ ((real_le (x0 x3 x1) x1) /\ (@IN real x2 x3))).
Definition term348 (x0 : Prop) (x1 : type1028) := x0 \/ (exists y0 : real -> real, x1 y0).
Definition term477 (x0 : Prop) (x1 : real -> Prop) := forall y0 : real, x0 \/ (x1 y0).
Definition term288 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le y0 x1) x2.
Definition term152 (x0 : real -> Prop) := exists y0 : real, (exists y1 : real, exists y2 : real, (@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y1)))) /\ (~ (real_le y0 (sup x0))).
Definition term135 (x0 : real) (x1 : real -> Prop) := exists y0 : real, (exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) /\ (~ (real_le x0 (sup x1))).
Definition term293 (x0 : real -> Prop) := ~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term390 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)) x2 (x1 x2).
Definition term335 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x2 (x1 x2).
Definition term121 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => (@IN real y0 x1) /\ ((real_le x0 y0) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x2))).
Definition term280 (x0 : type1023) := (forall y0 : real -> Prop, (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real))) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term219 := (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term514 (x0 : type1021) (x1 : real -> Prop) := (forall y0 : real, (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term382 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)) x1.
Definition term602 (x0 : type1021) (x1 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, forall y2 : real, ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0)))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))))) /\ (((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2)))) /\ ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2)))))) x1.
Definition term297 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) y0).
Definition term104 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((@IN real y3 x0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 x0) -> real_le y4 y2))) -> real_le y1 (sup x0)) y0).
Definition term97 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (@IN real y3 x1) -> real_le y3 y1))) -> real_le x0 (sup x1)) y0).
Definition term66 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real => ((@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (@IN real y1 x2) -> real_le y1 x0))) -> real_le x1 (sup x2).
Definition term484 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))).
Definition term483 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((x1 = (@EMPTY real)) \/ (forall y0 : real, (fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0)).
Definition term461 (x0 : type1021) := forall y0 : real -> Prop, ((y0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 (sup y0))) /\ (forall y1 : real, ((@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1))) \/ (real_le (sup y0) y1))).
Definition term321 := forall y0 : real -> Prop, ((y0 = (@EMPTY real)) \/ (forall y1 : real, exists y2 : real, (@IN real y2 y0) /\ (~ (real_le y2 y1)))) \/ ((forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 (sup y0))) /\ (forall y1 : real, (exists y2 : real, (@IN real y2 y0) /\ (~ (real_le y2 y1))) \/ (real_le (sup y0) y1))).
Definition term252 := fun y0 : real -> Prop => exists y1 : real, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y0 y1.
Definition term298 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term98 (x0 : real) (x1 : real -> Prop) := fun y0 : real => exists y1 : real, ((@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) /\ (~ (real_le x0 (sup x1))).
Definition term269 := (exists y0 : type1023, (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term557 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ (((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)) /\ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)))).
Definition term578 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1)))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))))) /\ (((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1)))) /\ ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))))).
Definition term546 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term68 (x0 : real) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, ((@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (@IN real y2 x1) -> real_le y2 y0))) -> real_le x0 (sup x1).
Definition term111 (x0 : real -> Prop) := ~ ((fun y0 : real -> Prop => forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0)) x0).
Definition term391 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x2))) \/ (real_le (sup x0) x2)) (x1 x2).
Definition term30 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term270 := exists y0 : type1023, ((fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0) /\ (forall y1 : real -> Prop, (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))).
Definition term446 := fun y0 : real -> Prop => fun y1 : real -> real => ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term17 := ~ (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)).
Definition term657 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (~ (@IN real x1 x0))) -> real_le x1 x2.
Definition term409 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0.
Definition term354 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0.
Definition term273 := exists y0 : type1023, (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0.
Definition term11 := forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real))).
Definition term444 := forall y0 : real -> Prop, exists y1 : real -> real, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y0 y1.
Definition term442 (x0 : type1017) := forall y0 : real -> Prop, exists y1 : real -> real, x0 y0 y1.
Definition term244 := forall y0 : real -> Prop, exists y1 : real, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y0 y1.
Definition term242 (x0 : type1020) := forall y0 : real -> Prop, exists y1 : real, x0 y0 y1.
Definition term15 := (((~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False) -> ((~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False.
Definition term456 (x0 : type1021) (x1 : real -> Prop) := (fun y0 : real -> real => ((x1 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x1) /\ (~ (real_le (y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (forall y1 : real, ((@IN real (y0 y1) x1) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x1) y1)))) (x0 x1).
Definition term100 (x0 : real -> Prop) := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (@IN real y3 x0) -> real_le y3 y1))) -> real_le y0 (sup x0)).
Definition term93 (x0 : real) (x1 : real -> Prop) := ~ (forall y0 : real, forall y1 : real, ((@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (@IN real y2 x1) -> real_le y2 y0))) -> real_le x0 (sup x1)).
Definition term612 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((@IN real (x0 x3 x1) x3) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term198 (x0 : type1022) (x1 : type1022) := forall y0 : real -> Prop, (x0 y0) /\ (x1 y0).
Definition term675 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (real_le x2 (sup x3)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))).
Definition term223 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) \/ x1.
Definition term687 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := imp (~ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))))).
Definition term13 := ((~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False.
Definition term685 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (real_le (x0 x3 x1) x1) /\ (@IN real x2 x3).
Definition term202 := fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term178 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term669 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := @eq Prop ((x2 = (@EMPTY real)) \/ ((real_le x0 (sup x2)) \/ ((~ (@IN real x0 x2)) \/ (~ (real_le (x1 x2 x3) x3))))).
Definition term34 (x0 : real -> Prop) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0.
Definition term179 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => @IN real y1 x0) y0).
Definition term454 := @eq Prop (forall y0 : real -> Prop, exists y1 : real -> real, ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2)))).
Definition term453 := @eq Prop (forall y0 : real -> Prop, exists y1 : real -> real, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y0 y1).
Definition term254 := @eq Prop (forall y0 : real -> Prop, exists y1 : real, (@IN real y1 y0) \/ (y0 = (@EMPTY real))).
Definition term253 := @eq Prop (forall y0 : real -> Prop, exists y1 : real, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y0 y1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term473 (x0 : type1021) (x1 : real -> Prop) := or ((x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))).
Definition term434 (x0 : real -> Prop) (x1 : real -> real) := or ((x0 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0)))).
Definition term317 (x0 : real -> Prop) := or ((x0 = (@EMPTY real)) \/ (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)))).
Definition term133 (x0 : real) (x1 : real) (x2 : real -> Prop) := (exists y0 : real, (@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 x0)))) /\ (~ (real_le x1 (sup x2))).
Definition term389 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)).
Definition term388 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y0 y1).
Definition term334 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))).
Definition term333 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1).
Definition term526 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)))).
Definition term525 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0) \/ (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)))).
Definition term250 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real -> Prop => fun y2 : real => (@IN real y2 y1) \/ (y1 = (@EMPTY real))) x0 y0.
Definition term145 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => exists y2 : real, (@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (~ (@IN real y3 x1)) \/ (real_le y3 y1)))) y0.
Definition term384 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1)) x2.
Definition term347 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term187 (x0 : real -> Prop) := or (exists y0 : real, @IN real y0 x0).
Definition term559 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))).
Definition term21 := (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> ~ (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)).
Definition term184 (x0 : real -> Prop) := or (forall y0 : real, ~ (@IN real y0 x0)).
Definition term217 := forall y0 : real -> Prop, (fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0.
Definition term212 := forall y0 : real -> Prop, (fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0.
Definition term251 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real -> Prop => fun y2 : real => (@IN real y2 y1) \/ (y1 = (@EMPTY real))) x0 y0.
Definition term584 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ~ (@IN real y0 x0)) x1.
Definition term139 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) x2.
Definition term660 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (~ (real_le (x0 x1 x2) x2)) -> real_le (x0 x1 x2) x2.
Definition term65 (x0 : real) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((@IN real x0 x3) /\ ((real_le x2 x0) /\ (forall y0 : real, (@IN real y0 x3) -> real_le y0 x1))) -> real_le x2 (sup x3).
Definition term640 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term666 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (real_le x0 (sup x2)) \/ ((~ (@IN real x0 x2)) \/ (~ (real_le (x1 x2 x3) x3))).
Definition term468 (x0 : type1021) (x1 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)).
Definition term413 (x0 : real -> real) (x1 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le (sup x1) y0)).
Definition term315 (x0 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)).
Definition term39 (x0 : real -> Prop) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0).
Definition term405 (x0 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0).
Definition term42 (x0 : real -> Prop) := and (~ (x0 = (@EMPTY real))).
Definition term163 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_le x1 x0) /\ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term142 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => exists y2 : real, (@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (~ (@IN real y3 x1)) \/ (real_le y3 y1)))) y0) /\ (~ (real_le x0 (sup x1))).
Definition term422 (x0 : real -> Prop) := (exists y0 : real -> real, (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0) \/ (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0).
Definition term565 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 x2) x2)).
Definition term630 (x0 : real) (x1 : real -> Prop) := (real_le x0 (sup x1)) \/ (~ (@IN real x0 x1)).
Definition term346 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term361 (x0 : real -> Prop) := exists y0 : real -> real, (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term618 (x0 : real) (x1 : real -> Prop) := @eq Prop ((~ (@IN real x0 x1)) \/ (~ (x1 = (@EMPTY real)))).
Definition term274 := and (exists y0 : type1023, (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term517 (x0 : real -> Prop) (x1 : Prop) := (forall y0 : real, x0 y0) \/ x1.
Definition term383 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)) x1 x2.
Definition term328 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x1 x2.
Definition term138 (x0 : real) (x1 : real -> Prop) := fun y0 : real => exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0))).
Definition term172 (x0 : real -> Prop) := ~ (ex x0).
Definition term587 (x0 : real -> Prop) := or (forall y0 : real, (fun y1 : real => ~ (@IN real y1 x0)) y0).
Definition term524 (x0 : type1021) (x1 : real -> Prop) := or (forall y0 : real, (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0).
Definition term14 := (((~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False.
Definition term263 := fun y0 : type1023 => forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real)).
Definition term359 (x0 : real -> Prop) := fun y0 : real -> real => (x0 = (@EMPTY real)) \/ ((fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term487 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (x1 = (@EMPTY real)) \/ ((fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0).
Definition term279 (x0 : type1023) := ((fun y0 : type1023 => forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) x0) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term583 (x0 : real -> Prop) := forall y0 : real, ((fun y1 : real => ~ (@IN real y1 x0)) y0) \/ (~ (x0 = (@EMPTY real))).
Definition term452 := fun y0 : real -> Prop => exists y1 : real -> real, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y0 y1.
Definition term379 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y0 y1.
Definition term378 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term324 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1.
Definition term322 (x0 : type1626) := forall y0 : real, exists y1 : real, x0 y0 y1.
Definition term299 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term690 (x0 : real) (x1 : real -> Prop) := (~ (real_le x0 (sup x1))) -> real_le x0 (sup x1).
Definition term593 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) \/ (~ (x1 = (@EMPTY real))).
Definition term186 (x0 : real -> Prop) := (forall y0 : real, ~ (@IN real y0 x0)) \/ (~ (x0 = (@EMPTY real))).
Definition term574 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := and ((((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))) /\ (((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))))).
Definition term62 (x0 : real) (x1 : real -> Prop) := and (@IN real x0 x1).
Definition term151 (x0 : real -> Prop) := fun y0 : real => (exists y1 : real, exists y2 : real, (@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y1)))) /\ (~ (real_le y0 (sup x0))).
Definition term134 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) /\ (~ (real_le x0 (sup x1))).
Definition term350 (x0 : real -> Prop) := (x0 = (@EMPTY real)) \/ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term420 (x0 : type1028) (x1 : type1028) := (exists y0 : real -> real, x0 y0) \/ (exists y0 : real -> real, x1 y0).
Definition term451 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> Prop => fun y2 : real -> real => ((y1 = (@EMPTY real)) \/ (forall y3 : real, (@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3)))) \/ ((forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y3 (sup y1))) /\ (forall y3 : real, ((@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3))) \/ (real_le (sup y1) y3)))) x0 y0.
Definition term277 (x0 : type1023) := and ((fun y0 : type1023 => forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) x0).
Definition term704 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term233 (x0 : real) (x1 : real -> Prop) := ((fun y0 : real => @IN real y0 x1) x0) \/ (x1 = (@EMPTY real)).
Definition term47 (x0 : real -> Prop) := ~ (x0 = (@EMPTY real)).
Definition term268 (x0 : type257) (x1 : Prop) := exists y0 : type1023, (x0 y0) /\ x1.
Definition term36 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) -> real_le y0 (sup x0).
Definition term144 (x0 : real) (x1 : real -> Prop) := @eq Prop (exists y0 : real, (exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) /\ (~ (real_le x0 (sup x1)))).
Definition term143 (x0 : real) (x1 : real -> Prop) := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, (@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (~ (@IN real y3 x1)) \/ (real_le y3 y1)))) y0) /\ (~ (real_le x0 (sup x1)))).
Definition term127 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop (exists y0 : real, ((@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 x0)))) /\ (~ (real_le x1 (sup x2)))).
Definition term126 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop (exists y0 : real, ((fun y1 : real => (@IN real y1 x2) /\ ((real_le x1 y1) /\ (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 x0)))) y0) /\ (~ (real_le x1 (sup x2)))).
Definition term302 (x0 : real -> Prop) := (~ (~ (x0 = (@EMPTY real)))) \/ (~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term35 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) -> real_le x0 (sup x1).
Definition term27 (x0 : real -> Prop) (x1 : real) := real_le (sup x0) x1.
Definition term542 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2))) /\ (((@IN real (x1 x2 x3) x2) /\ (~ (real_le (x1 x2 x3) x3))) \/ (real_le (sup x2) x3))).
Definition term435 (x0 : real -> Prop) (x1 : real -> real) := ((fun y0 : real -> real => (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) x1) \/ ((fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))) x1).
Definition term168 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term55 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term40 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0.
Definition term374 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0) \/ (real_le (sup x0) x1).
Definition term336 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x2))) (x1 x2).
Definition term85 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term492 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term16 := (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False.
Definition term289 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (@IN real y0 x0) -> real_le y0 x1) x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term705 (x0 : real) (x1 : real) (x2 : real -> Prop) := (real_le x0 x1) /\ (real_le x1 (sup x2)).
Definition term582 (x0 : real -> Prop) := (forall y0 : real, (fun y1 : real => ~ (@IN real y1 x0)) y0) \/ (~ (x0 = (@EMPTY real))).
Definition term136 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((fun y1 : real => exists y2 : real, (@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (~ (@IN real y3 x1)) \/ (real_le y3 y1)))) y0) /\ (~ (real_le x0 (sup x1))).
Definition term119 (x0 : real) (x1 : real) (x2 : real -> Prop) := exists y0 : real, ((fun y1 : real => (@IN real y1 x2) /\ ((real_le x1 y1) /\ (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 x0)))) y0) /\ (~ (real_le x1 (sup x2))).
Definition term221 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term625 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term376 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ((@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1).
Definition term305 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) \/ (real_le x0 (sup x1)).
Definition term318 (x0 : real -> Prop) := (~ ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0))) \/ ((forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0)).
Definition term621 (x0 : real) (x1 : real -> Prop) := (~ (~ (@IN real x0 x1))) -> ~ (x1 = (@EMPTY real)).
Definition term92 (x0 : real) (x1 : real) (x2 : real -> Prop) := exists y0 : real, ((@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 x0)))) /\ (~ (real_le x1 (sup x2))).
Definition term634 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((@IN real (x0 x3 x1) x3) \/ ((real_le x2 (sup x3)) \/ (~ (@IN real x2 x3)))).
Definition term472 (x0 : type1021) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))).
Definition term586 (x0 : real -> Prop) := forall y0 : real, (fun y1 : real => ~ (@IN real y1 x0)) y0.
Definition term529 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := ((fun y0 : real => (x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0)))) x0) \/ (forall y0 : real, ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))).
Definition term238 := fun y0 : real -> Prop => exists y1 : real, (@IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term153 := fun y0 : real -> Prop => exists y1 : real, (exists y2 : real, exists y3 : real, (@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (~ (@IN real y4 y0)) \/ (real_le y4 y2)))) /\ (~ (real_le y1 (sup y0))).
Definition term195 := forall y0 : real -> Prop, ((exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) /\ ((forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term623 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term216 := fun y0 : real -> Prop => (fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0.
Definition term303 (x0 : real -> Prop) := (x0 = (@EMPTY real)) \/ (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))).
Definition term664 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (real_le x0 (sup x2)) \/ (~ (real_le (x1 x2 x3) x3)).
Definition term162 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term89 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := ~ ((fun y0 : real => ((@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (@IN real y1 x2) -> real_le y1 x0))) -> real_le x1 (sup x2)) x3).
Definition term545 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := forall y0 : real, ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))).
Definition term140 (x0 : real) (x1 : real -> Prop) (x2 : real) := and ((fun y0 : real => exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) x2).
Definition term9 := (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> False.
Definition term538 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (fun y1 : real => ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))) y0.
Definition term523 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0.
Definition term501 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0.
Definition term497 (x0 : real -> Prop) := forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) y0.
Definition term482 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0.
Definition term209 := @eq Prop (forall y0 : real -> Prop, ((fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0) /\ ((fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0)).
Definition term594 (x0 : real -> Prop) := fun y0 : real => ((fun y1 : real => ~ (@IN real y1 x0)) y0) \/ (~ (x0 = (@EMPTY real))).
Definition term256 (x0 : type1023) (x1 : real -> Prop) := (fun y0 : real => (@IN real y0 x1) \/ (x1 = (@EMPTY real))) (x0 x1).
Definition term635 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((x3 = (@EMPTY real)) \/ ((@IN real (x0 x3 x1) x3) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))))).
Definition term544 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := fun y0 : real => ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))).
Definition term12 := (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> False.
Definition term28 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) -> real_le x1 x2.
Definition term421 (x0 : type1028) (x1 : type1028) := exists y0 : real -> real, (x0 y0) \/ (x1 y0).
Definition term590 (x0 : real -> Prop) (x1 : real) := or ((fun y0 : real => ~ (@IN real y0 x0)) x1).
Definition term516 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term650 (x0 : real) (x1 : real -> Prop) := imp ((~ (x1 = (@EMPTY real))) /\ ((@IN real x0 x1) /\ (~ (real_le x0 (sup x1))))).
Definition term653 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := ~ (@IN real (x0 x2 x1) x2).
Definition term512 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((fun y0 : Prop => y0 = (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)))) ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)))).
Definition term46 := fun y0 : real -> Prop => ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1).
Definition term32 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1) -> real_le (sup x0) x1.
Definition term671 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((real_le x2 (sup x3)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)))).
Definition term351 (x0 : real -> Prop) := exists y0 : real -> real, (x0 = (@EMPTY real)) \/ ((fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term459 (x0 : type1021) := fun y0 : real -> Prop => ((y0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 (sup y0))) /\ (forall y1 : real, ((@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1))) \/ (real_le (sup y0) y1))).
Definition term320 := fun y0 : real -> Prop => ((y0 = (@EMPTY real)) \/ (forall y1 : real, exists y2 : real, (@IN real y2 y0) /\ (~ (real_le y2 y1)))) \/ ((forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 (sup y0))) /\ (forall y1 : real, (exists y2 : real, (@IN real y2 y0) /\ (~ (real_le y2 y1))) \/ (real_le (sup y0) y1))).
Definition term604 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (fun y0 : real => ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2)))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))))) /\ (((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0)))))) x3.
Definition term479 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (x1 = (@EMPTY real)) \/ ((fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0).
Definition term375 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1).
Definition term506 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((fun y0 : real => (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) x2) /\ ((fun y0 : real => ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)) x2).
Definition term64 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := imp ((@IN real x1 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le y0 x3))).
Definition term693 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term568 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := and ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))).
Definition term271 (x0 : type1023) := (fun y0 : type1023 => forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) x0.
Definition term600 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1)) x1.
Definition term295 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) x1.
Definition term372 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((fun y0 : real => (@IN real y0 x1) /\ (~ (real_le y0 x2))) x0) \/ (real_le (sup x1) x2).
Definition term307 (x0 : real -> Prop) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0)).
Definition term702 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term646 (x0 : real) (x1 : real -> Prop) := and (~ (~ (@IN real x0 x1))).
Definition term406 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ ((fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0).
Definition term177 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => @IN real y0 x0) x1).
Definition term206 (x0 : real -> Prop) := (fun y0 : real -> Prop => (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))) x0.
Definition term698 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2)))) -> real_le x1 x2.
Definition term141 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((fun y0 : real => exists y1 : real, (@IN real y1 x2) /\ ((real_le x1 y1) /\ (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 y0)))) x0) /\ (~ (real_le x1 (sup x2))).
Definition term211 := fun y0 : real -> Prop => (fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0.
Definition term246 := fun y0 : real -> Prop => fun y1 : real => (@IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term667 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((real_le x0 (sup x2)) \/ ((~ (@IN real x0 x2)) \/ (~ (real_le (x1 x2 x3) x3)))).
Definition term385 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le (sup x0) y1)) x1 y0.
Definition term330 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) x1 y0.
Definition term519 (x0 : type1021) (x1 : real -> Prop) := (forall y0 : real, (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0) \/ (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term166 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term552 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ~ (real_le (x0 x1 x2) x2).
Definition term203 := fun y0 : real -> Prop => (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))).
Definition term395 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le (sup x0) y1)) y0 (x1 y0).
Definition term340 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) y0 (x1 y0).
Definition term505 (x0 : real) (x1 : real -> Prop) := and ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1))).
Definition term673 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ (@IN real x0 x2)) \/ (~ (real_le (x1 x2 x3) x3)).
Definition term533 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term692 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ (~ (real_le x1 x2)).
Definition term486 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2))).
Definition term652 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (~ (@IN real (x0 x2 x1) x2)) -> @IN real (x0 x2 x1) x2.
Definition term415 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)).
Definition term255 (x0 : type1023) (x1 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real => (@IN real y1 y0) \/ (y0 = (@EMPTY real))) x1 (x0 x1).
Definition term249 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real y0 x0) \/ (x0 = (@EMPTY real))) x1.
Definition term563 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))).
Definition term678 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ~ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)))).
Definition term460 (x0 : type1021) := forall y0 : real -> Prop, (fun y1 : real -> Prop => fun y2 : real -> real => ((y1 = (@EMPTY real)) \/ (forall y3 : real, (@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3)))) \/ ((forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y3 (sup y1))) /\ (forall y3 : real, ((@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3))) \/ (real_le (sup y1) y3)))) y0 (x0 y0).
Definition term260 (x0 : type1023) := forall y0 : real -> Prop, (fun y1 : real -> Prop => fun y2 : real => (@IN real y2 y1) \/ (y1 = (@EMPTY real))) y0 (x0 y0).
Definition term633 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (@IN real (x0 x3 x1) x3) \/ ((real_le x2 (sup x3)) \/ (~ (@IN real x2 x3))).
Definition term598 := forall y0 : real -> Prop, forall y1 : real, (~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))).
Definition term267 (x0 : type257) (x1 : Prop) := (exists y0 : type1023, x0 y0) /\ x1.
Definition term118 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term603 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => forall y1 : real, ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1)))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))))) /\ (((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1)))) /\ ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1)))))) x2.
Definition term95 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => forall y1 : real, ((@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (@IN real y2 x1) -> real_le y2 y0))) -> real_le x0 (sup x1)) x2.
Definition term112 := fun y0 : real -> Prop => ~ ((fun y1 : real -> Prop => forall y2 : real, forall y3 : real, forall y4 : real, ((@IN real y4 y1) /\ ((real_le y2 y4) /\ (forall y5 : real, (@IN real y5 y1) -> real_le y5 y3))) -> real_le y2 (sup y1)) y0).
Definition term218 := forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))).
Definition term207 (x0 : real -> Prop) := ((fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) x0) /\ ((fun y0 : real -> Prop => (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))) x0).
Definition term561 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (~ (real_le (x0 x1 x2) x2)) \/ (real_le (sup x1) x2).
Definition term259 (x0 : type1023) := fun y0 : real -> Prop => (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real)).
Definition term569 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := and ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)))).
Definition term377 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term194 := fun y0 : real -> Prop => ((exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) /\ ((forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term662 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (@IN real x2 x3)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (real_le x2 (sup x3))).
Definition term170 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term70 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, forall y2 : real, ((@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (@IN real y3 x0) -> real_le y3 y1))) -> real_le y0 (sup x0).
Definition term57 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term509 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)).
Definition term296 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) x1).
Definition term103 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, ((@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (@IN real y3 x0) -> real_le y3 y1))) -> real_le y0 (sup x0)) x1).
Definition term105 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, exists y2 : real, ((@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (~ (@IN real y3 x0)) \/ (real_le y3 y1)))) /\ (~ (real_le y0 (sup x0))).
Definition term278 (x0 : type1023) := and (forall y0 : real -> Prop, (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real))).
Definition term215 := and (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))).
Definition term158 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((exists y0 : real, (@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 x0)))) /\ (~ (real_le x1 (sup x2)))).
Definition term157 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => (@IN real y1 x2) /\ ((real_le x1 y1) /\ (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 x0)))) y0) /\ (~ (real_le x1 (sup x2)))).
Definition term156 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) /\ (~ (real_le x0 (sup x1)))).
Definition term155 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, (@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (~ (@IN real y3 x1)) \/ (real_le y3 y1)))) y0) /\ (~ (real_le x0 (sup x1)))).
Definition term597 := fun y0 : real -> Prop => forall y1 : real, (~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))).
Definition term398 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1).
Definition term397 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y1 (y0 y1).
Definition term343 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)).
Definition term342 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y1 (y0 y1).
Definition term192 (x0 : real -> Prop) := ((exists y0 : real, @IN real y0 x0) \/ (~ (~ (x0 = (@EMPTY real))))) /\ ((~ (exists y0 : real, @IN real y0 x0)) \/ (~ (x0 = (@EMPTY real)))).
Definition term706 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((real_le x1 x0) /\ (real_le x0 (sup x2))) -> real_le x1 (sup x2).
Definition term656 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((real_le x1 x0) \/ (~ (@IN real x1 x2))).
Definition term638 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (~ ((x3 = (@EMPTY real)) \/ ((~ (@IN real x0 x3)) \/ (real_le x0 (sup x3))))) -> @IN real (x1 x3 x2) x3.
Definition term110 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0)) x0.
Definition term174 (x0 : real -> Prop) := ~ (exists y0 : real, @IN real y0 x0).
Definition term91 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real => ((@IN real y0 x2) /\ ((real_le x1 y0) /\ (forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y1 x0)))) /\ (~ (real_le x1 (sup x2))).
Definition term679 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (x3 = (@EMPTY real))) /\ (~ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)))).
Definition term636 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((x3 = (@EMPTY real)) \/ ((@IN real (x0 x3 x1) x3) \/ ((real_le x2 (sup x3)) \/ (~ (@IN real x2 x3))))).
Definition term427 (x0 : real -> Prop) := or (exists y0 : real -> real, (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0).
Definition term611 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term122 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (fun y0 : real => (@IN real y0 x1) /\ ((real_le x0 y0) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x2)))) x3.
Definition term292 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1)).
Definition term234 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) \/ (x1 = (@EMPTY real)).
Definition term180 (x0 : real -> Prop) := fun y0 : real => ~ (@IN real y0 x0).
Definition term312 (x0 : real -> Prop) := fun y0 : real => (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term226 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => @IN real y1 x0) y0.
Definition term699 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term680 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ~ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))).
Definition term54 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term49 (x0 : real -> Prop) := exists y0 : real, @IN real y0 x0.
Definition term556 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ (((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2))) /\ (((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)) /\ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)))).
Definition term489 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))).
Definition term201 := (forall y0 : real -> Prop, (fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0) /\ (forall y0 : real -> Prop, (fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0).
Definition term564 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (x2 = (@EMPTY real)) \/ (@IN real (x0 x2 x1) x2).
Definition term658 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (@IN real (x0 x1 x2) x1) -> real_le (x0 x1 x2) x2.
Definition term148 (x0 : real) (x1 : real -> Prop) := and (exists y0 : real, (fun y1 : real => exists y2 : real, (@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (~ (@IN real y3 x1)) \/ (real_le y3 y1)))) y0).
Definition term131 (x0 : real) (x1 : real -> Prop) (x2 : real) := and (exists y0 : real, (fun y1 : real => (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 x2)))) y0).
Definition term619 (x0 : real) (x1 : real -> Prop) := @eq Prop ((~ (x1 = (@EMPTY real))) \/ (~ (@IN real x0 x1))).
Definition term537 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))) y0.
Definition term128 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => (fun y1 : real => (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 x2)))) y0.
Definition term150 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))) /\ (~ (real_le x0 (sup x1))).
Definition term428 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))) x1.
Definition term123 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := and ((fun y0 : real => (@IN real y0 x1) /\ ((real_le x0 y0) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x2)))) x3).
Definition term326 (x0 : real -> Prop) := fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term423 (x0 : real -> Prop) := exists y0 : real -> real, ((fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0) \/ ((fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0).
Definition term83 (x0 : real) (x1 : real) (x2 : real) (x3 : real -> Prop) := ~ (((@IN real x0 x3) /\ ((real_le x2 x0) /\ (forall y0 : real, (@IN real y0 x3) -> real_le y0 x1))) -> real_le x2 (sup x3)).
Definition term60 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term508 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) y0) /\ ((fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0).
Definition term500 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0.
Definition term553 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((~ (@IN real x2 x1)) \/ (real_le x2 (sup x1))) /\ (((@IN real (x0 x1 x2) x1) \/ (real_le (sup x1) x2)) /\ ((~ (real_le (x0 x1 x2) x2)) \/ (real_le (sup x1) x2))).
Definition term649 (x0 : real) (x1 : real -> Prop) := imp (~ ((x1 = (@EMPTY real)) \/ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1))))).
Definition term165 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term543 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := fun y0 : real => ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ ((fun y1 : real => ((~ (@IN real y1 x2)) \/ (real_le y1 (sup x2))) /\ (((@IN real (x1 x2 y1) x2) /\ (~ (real_le (x1 x2 y1) y1))) \/ (real_le (sup x2) y1))) y0).
Definition term577 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := forall y0 : real, ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2)))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))))) /\ (((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))))).
Definition term329 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1))) x2.
Definition term294 (x0 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) y0).
Definition term175 (x0 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => @IN real y1 x0) y0).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term31 (x0 : real -> Prop) (x1 : real) := imp (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term458 (x0 : type1021) := fun y0 : real -> Prop => (fun y1 : real -> Prop => fun y2 : real -> real => ((y1 = (@EMPTY real)) \/ (forall y3 : real, (@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3)))) \/ ((forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y3 (sup y1))) /\ (forall y3 : real, ((@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3))) \/ (real_le (sup y1) y3)))) y0 (x0 y0).
Definition term258 (x0 : type1023) := fun y0 : real -> Prop => (fun y1 : real -> Prop => fun y2 : real => (@IN real y2 y1) \/ (y1 = (@EMPTY real))) y0 (x0 y0).
Definition term616 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) -> @IN real x0 x1.
Definition term290 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 x1) y0).
Definition term90 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => ((@IN real y1 x2) /\ ((real_le x1 y1) /\ (forall y2 : real, (@IN real y2 x2) -> real_le y2 x0))) -> real_le x1 (sup x2)) y0).
Definition term450 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> Prop => fun y2 : real -> real => ((y1 = (@EMPTY real)) \/ (forall y3 : real, (@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3)))) \/ ((forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y3 (sup y1))) /\ (forall y3 : real, ((@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3))) \/ (real_le (sup y1) y3)))) x0 y0.
Definition term469 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2)).
Definition term102 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((@IN real y2 x0) /\ ((real_le y0 y2) /\ (forall y3 : real, (@IN real y3 x0) -> real_le y3 y1))) -> real_le y0 (sup x0)) x1.
Definition term37 (x0 : real -> Prop) := forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0).
Definition term491 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term448 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> Prop => fun y1 : real -> real => ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2)))) x0 x1.
Definition term285 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) /\ (~ (real_le x1 x2)).
Definition term639 (x0 : real) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1))).
Definition term300 (x0 : real -> Prop) := or (~ (~ (x0 = (@EMPTY real)))).
Definition term313 (x0 : real -> Prop) := forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term48 (x0 : real -> Prop) := fun y0 : real => @IN real y0 x0.
Definition term576 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := fun y0 : real => ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2)))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))))) /\ (((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))))).
Definition term214 := and (forall y0 : real -> Prop, (fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0).
Definition term411 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))).
Definition term410 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0)).
Definition term196 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term642 (x0 : real) (x1 : real -> Prop) := ~ ((x1 = (@EMPTY real)) \/ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1)))).
Definition term554 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 x2) x1)) /\ ((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 x2) x2))).
Definition term225 (x0 : real -> Prop) := exists y0 : real, ((fun y1 : real => @IN real y1 x0) y0) \/ (x0 = (@EMPTY real)).
Definition term231 (x0 : real -> Prop) (x1 : real) := or ((fun y0 : real => @IN real y0 x0) x1).
Definition term655 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((~ (@IN real x1 x0)) \/ (real_le x1 x2)).
Definition term592 (x0 : real) (x1 : real -> Prop) := ((fun y0 : real => ~ (@IN real y0 x1)) x0) \/ (~ (x1 = (@EMPTY real))).
Definition term108 (x0 : type1022) := exists y0 : real -> Prop, ~ (x0 y0).
Definition term327 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x1.
Definition term276 := @eq Prop ((exists y0 : type1023, forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))))).
Definition term275 := @eq Prop ((exists y0 : type1023, (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))))).
Definition term306 (x0 : real -> Prop) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0)).
Definition term272 := fun y0 : type1023 => (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0.
Definition term478 (x0 : type1021) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ (forall y0 : real, (fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0).
Definition term363 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0) \/ (real_le (sup x0) x1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term53 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term189 (x0 : real -> Prop) := (exists y0 : real, @IN real y0 x0) \/ (x0 = (@EMPTY real)).
Definition term631 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := or (@IN real (x0 x2 x1) x2).
Definition term183 (x0 : real -> Prop) := or (~ (exists y0 : real, @IN real y0 x0)).
Definition term694 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ ((real_le x0 x2) \/ (~ (real_le x1 x2))).
Definition term237 (x0 : real -> Prop) := exists y0 : real, (@IN real y0 x0) \/ (x0 = (@EMPTY real)).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term684 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := and (real_le (x0 x1 x2) x2).
Definition term149 (x0 : real) (x1 : real -> Prop) := and (exists y0 : real, exists y1 : real, (@IN real y1 x1) /\ ((real_le x0 y1) /\ (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y2 y0)))).
Definition term595 (x0 : real -> Prop) := fun y0 : real => (~ (@IN real y0 x0)) \/ (~ (x0 = (@EMPTY real))).
Definition term674 (x0 : real) (x1 : real -> Prop) := or (real_le x0 (sup x1)).
Definition term531 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0) \/ (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term371 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((@IN real x1 x0) /\ (~ (real_le x1 x2))).
Definition term480 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) x2.
Definition term386 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le (sup x0) y1)) x1 y0.
Definition term331 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) x1 y0.
Definition term369 (x0 : real -> Prop) (x1 : real) := @eq Prop ((exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1)).
Definition term368 (x0 : real -> Prop) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0) \/ (real_le (sup x0) x1)).
Definition term465 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2))) \/ (real_le (sup x1) x2).
Definition term392 (x0 : real -> real) (x1 : real -> Prop) (x2 : real) := ((@IN real (x0 x2) x1) /\ (~ (real_le (x0 x2) x2))) \/ (real_le (sup x1) x2).
Definition term373 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((@IN real x0 x1) /\ (~ (real_le x0 x2))) \/ (real_le (sup x1) x2).
Definition term362 (x0 : real -> Prop) := or (exists y0 : real -> real, (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))).
Definition term541 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ ((fun y0 : real => ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))) x3).
Definition term663 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (real_le (x0 x3 x1) x1)) \/ (real_le x2 (sup x3)).
Definition term291 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1)).
Definition term504 (x0 : real -> Prop) (x1 : real) := and ((fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) x1).
Definition term235 (x0 : real -> Prop) := fun y0 : real => ((fun y1 : real => @IN real y1 x0) y0) \/ (x0 = (@EMPTY real)).
Definition term159 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term381 (x0 : real -> Prop) := fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term78 (x0 : real) (x1 : real -> Prop) := ~ (real_le x0 (sup x1)).
Definition term51 := fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real))).
Definition term691 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ (real_le x1 x2).
Definition term241 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term284 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((@IN real x1 x0) -> real_le x1 x2).
Definition term591 (x0 : real) (x1 : real -> Prop) := or (~ (@IN real x0 x1)).
Definition term677 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))).
Definition term309 (x0 : real -> Prop) (x1 : real) := or (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1))).
Definition term467 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0).
Definition term396 (x0 : real -> real) (x1 : real -> Prop) := forall y0 : real, ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le (sup x1) y0).
Definition term532 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term599 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2)) x0.
Definition term419 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term200 := forall y0 : real -> Prop, ((fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0) /\ ((fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0).
Definition term132 (x0 : real) (x1 : real -> Prop) (x2 : real) := and (exists y0 : real, (@IN real y0 x1) /\ ((real_le x0 y0) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x2)))).
Definition term125 (x0 : real) (x1 : real) (x2 : real -> Prop) := fun y0 : real => ((fun y1 : real => (@IN real y1 x2) /\ ((real_le x1 y1) /\ (forall y2 : real, (~ (@IN real y2 x2)) \/ (real_le y2 x0)))) y0) /\ (~ (real_le x1 (sup x2))).
Definition term707 (x0 : real) (x1 : real -> Prop) := (real_le x0 (sup x1)) -> False.
Definition term441 := forall y0 : real -> Prop, exists y1 : real -> real, ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term239 := forall y0 : real -> Prop, exists y1 : real, (@IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term627 (x0 : real -> Prop) := (x0 = (@EMPTY real)) -> ~ (x0 = (@EMPTY real)).
Definition term494 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((fun y1 : real => (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) y0) /\ ((fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0).
Definition term199 (x0 : type1022) (x1 : type1022) := (forall y0 : real -> Prop, x0 y0) /\ (forall y0 : real -> Prop, x1 y0).
Definition term695 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term310 (x0 : real -> Prop) (x1 : real) := (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) \/ (real_le (sup x0) x1).
Definition term534 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (forall y0 : real, (fun y1 : real => ((~ (@IN real y1 x2)) \/ (real_le y1 (sup x2))) /\ (((@IN real (x1 x2 y1) x2) /\ (~ (real_le (x1 x2 y1) y1))) \/ (real_le (sup x2) y1))) y0).
Definition term45 (x0 : real -> Prop) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0).
Definition term683 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := and (~ (~ (real_le (x0 x1 x2) x2))).
Definition term80 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := and ((@IN real x1 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le y0 x3)))).
Definition term79 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := and ((@IN real x1 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le y0 x3))).
Definition term282 := fun y0 : type1023 => (forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) /\ (forall y1 : real -> Prop, (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))).
Definition term447 (x0 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real -> real => ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2)))) x0.
Definition term575 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2)))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2))))) /\ (((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))))).
Definition term25 := imp (~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y1 y3) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y4 y2))) -> real_le y1 (sup y0))).
Definition term558 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ (((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)) /\ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))).
Definition term628 (x0 : Prop) := x0 -> ~ x0.
Definition term167 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term82 (x0 : real) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((@IN real x0 x3) /\ ((real_le x2 x0) /\ (forall y0 : real, (~ (@IN real y0 x3)) \/ (real_le y0 x1)))) /\ (~ (real_le x2 (sup x3))).
Definition term81 (x0 : real) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((@IN real x0 x3) /\ ((real_le x2 x0) /\ (forall y0 : real, (@IN real y0 x3) -> real_le y0 x1))) /\ (~ (real_le x2 (sup x3))).
Definition term358 (x0 : real -> Prop) (x1 : real -> real) := (x0 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0))).
Definition term43 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term160 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_le x1 x2)).
Definition term624 (x0 : real) (x1 : real -> Prop) := imp (~ (~ (@IN real x0 x1))).
Definition term227 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => @IN real y1 x0) y0.
Definition term146 (x0 : real) (x1 : real -> Prop) := exists y0 : real, (fun y1 : real => exists y2 : real, (@IN real y2 x1) /\ ((real_le x0 y2) /\ (forall y3 : real, (~ (@IN real y3 x1)) \/ (real_le y3 y1)))) y0.
Definition term550 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((@IN real (x0 x1 x2) x1) \/ (real_le (sup x1) x2)) /\ ((~ (real_le (x0 x1 x2) x2)) \/ (real_le (sup x1) x2)).
Definition term589 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (@IN real y0 x0)) \/ (~ (x0 = (@EMPTY real)))).
Definition term588 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (fun y1 : real => ~ (@IN real y1 x0)) y0) \/ (~ (x0 = (@EMPTY real)))).
Definition term686 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (x3 = (@EMPTY real))) /\ ((real_le (x0 x3 x1) x1) /\ (@IN real x2 x3)).
Definition term432 (x0 : real -> Prop) := @eq Prop ((exists y0 : real -> real, (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ (exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)))).
Definition term431 (x0 : real -> Prop) := @eq Prop ((exists y0 : real -> real, (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0) \/ (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0)).
