Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term741 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = x0) /\ ((x2 = x1) /\ (@IN real x2 x3)).
Definition term149 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((@IN real x0 x2) /\ (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le y0 x0))) /\ ((~ (@IN real (sup x2) x2)) \/ ((@IN real x1 x2) /\ (~ (real_le x1 (sup x2))))).
Definition term39 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term566 (x0 : real) (x1 : real -> Prop) := (~ (~ (@IN real x0 x1))) /\ (~ (real_le x0 (sup x1))).
Definition term142 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((@IN real x0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x0))) /\ ((fun y1 : real => (~ (@IN real (sup x1) x1)) \/ ((@IN real y1 x1) /\ (~ (real_le y1 (sup x1))))) y0).
Definition term425 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))).
Definition term659 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (real_le (x0 x2 x1) x1) /\ (~ (real_le (sup x2) x3)).
Definition term306 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0.
Definition term302 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0.
Definition term122 (x0 : real -> Prop) := (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1))) y0) /\ (exists y0 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y0 x0) /\ (~ (real_le y0 (sup x0))))).
Definition term520 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1)) x2.
Definition term742 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := imp (~ ((~ (x3 = x0)) \/ ((~ (x2 = x1)) \/ (~ (@IN real x2 x3))))).
Definition term465 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (forall y0 : real, ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))).
Definition term36 := forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (~ ((exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (@IN real (sup y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)))) -> (forall y1 : real -> Prop, ((~ (y1 = (@EMPTY real))) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2)) -> (forall y2 : real, (@IN real y2 y1) -> real_le y2 (sup y1)) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> real_le (sup y1) y2)) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> ~ (forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) = (y1 = y2)).
Definition term35 := forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (~ ((exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (@IN real (sup y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)))) -> (forall y1 : real -> Prop, ((~ (y1 = (@EMPTY real))) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2)) -> (forall y2 : real, (@IN real y2 y1) -> real_le y2 (sup y1)) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> real_le (sup y1) y2)) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) = (y1 = y2)) -> False.
Definition term463 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := or ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2)))).
Definition term403 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0).
Definition term273 (x0 : real -> real) (x1 : real -> Prop) := fun y0 : real => ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le (sup x1) y0).
Definition term178 (x0 : real -> Prop) := ~ ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term495 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (@IN real (x0 x1 x2) x1) \/ (real_le (sup x1) x2).
Definition term82 (x0 : real -> Prop) := ~ (all x0).
Definition term750 := (~ False) -> False.
Definition term434 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)) x2.
Definition term689 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (~ (~ (real_le (x1 x3 x0) x0))) /\ (~ (@IN real (x1 x3 x2) x3)).
Definition term307 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0.
Definition term303 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0.
Definition term411 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term317 := fun y0 : real -> Prop => exists y1 : real -> real, ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term631 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (x2 = (@EMPTY real))) /\ (~ ((@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3))).
Definition term22 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term507 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))) /\ (((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term453 (x0 : real -> Prop) (x1 : Prop) := forall y0 : real, (x0 y0) \/ x1.
Definition term508 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := and ((((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) /\ ((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1)))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term114 (x0 : real -> Prop) := fun y0 : real => (~ (@IN real (sup x0) x0)) \/ ((fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 (sup x0)))) y0).
Definition term175 (x0 : real -> Prop) := or (x0 = (@EMPTY real)).
Definition term438 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term437 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) y0) /\ (forall y0 : real, (fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0)).
Definition term134 (x0 : real -> Prop) := fun y0 : real => ((fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1))) y0) /\ (exists y1 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y1 x0) /\ (~ (real_le y1 (sup x0))))).
Definition term8 (x0 : real -> Prop) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term314 (x0 : real -> Prop) := fun y0 : real -> real => ((fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0) \/ ((fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0).
Definition term595 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (real_le x2 (sup x3)) \/ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)))).
Definition term74 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term418 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0.
Definition term244 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0.
Definition term108 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 (sup x0)))) y0.
Definition term664 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (real_le (x0 x1 x2) x2) /\ (~ (real_le (sup x1) x2)).
Definition term644 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ (real_le (x1 x2 x0) x0)) \/ ((real_le (sup x2) x3) \/ (~ (real_le (x1 x2 x3) x3))).
Definition term567 (x0 : Prop) := ~ (~ x0).
Definition term80 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) /\ (~ (real_le x0 (sup x1))).
Definition term340 := fun y0 : type1021 => forall y1 : real -> Prop, ((y1 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y0 y1 y2) y1) /\ (~ (real_le (y0 y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 (sup y1))) /\ (forall y2 : real, ((@IN real (y0 y1 y2) y1) /\ (~ (real_le (y0 y1 y2) y2))) \/ (real_le (sup y1) y2))).
Definition term697 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((~ (x1 = (@EMPTY real))) /\ ((real_le (x0 x1 x2) x2) /\ (~ (@IN real (x0 x1 x2) x1)))) -> real_le (sup x1) x2.
Definition term397 := and (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))).
Definition term81 (x0 : real) (x1 : real -> Prop) := real_le x0 (sup x1).
Definition term155 (x0 : real -> Prop) := ~ (~ (x0 = (@EMPTY real))).
Definition term505 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)))).
Definition term76 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) /\ (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1)).
Definition term70 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term641 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (real_le (sup x1) x2) \/ (~ (real_le (x0 x1 x2) x2)).
Definition term222 (x0 : real -> Prop) := (x0 = (@EMPTY real)) \/ (exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term536 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := (@IN real x0 x1) \/ (~ (@IN real x2 x3)).
Definition term291 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ ((fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0).
Definition term486 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := @IN real (x0 x2 x1) x2.
Definition term139 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term497 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)).
Definition term675 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := @eq Prop ((x2 = (@EMPTY real)) \/ ((~ (real_le (x1 x2 x0) x0)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)))).
Definition term647 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := @eq Prop ((x2 = (@EMPTY real)) \/ ((~ (real_le (x1 x2 x0) x0)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)))).
Definition term652 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (real_le (x0 x2 x3) x3)) \/ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3)).
Definition term606 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (~ (real_le (x0 x3 x1) x1))) /\ (~ (~ (@IN real x2 x3))).
Definition term724 (x0 : real -> Prop) (x1 : real -> Prop) := ~ (x0 = x1).
Definition term375 (x0 : real) := and (forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))).
Definition term189 (x0 : real -> Prop) := and (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))).
Definition term57 (x0 : real -> Prop) := and (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)).
Definition term407 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)).
Definition term585 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (real_le (x0 x3 x1) x1)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term301 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) x1.
Definition term687 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (~ (x3 = (@EMPTY real))) /\ (~ ((~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3))).
Definition term656 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (x2 = (@EMPTY real))) /\ (~ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3))).
Definition term736 (x0 : real) (x1 : real) (x2 : real -> Prop) := (~ (~ (x1 = x0))) /\ (~ (~ (@IN real x1 x2))).
Definition term709 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term14 (x0 : real -> Prop) := ~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0))).
Definition term387 (x0 : real) := and ((fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0).
Definition term295 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term342 (x0 : real) (x1 : real) := ~ ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term92 (x0 : real -> Prop) := (~ (@IN real (sup x0) x0)) \/ (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0))).
Definition term446 (x0 : type1021) (x1 : real -> Prop) := (fun y0 : Prop => y0 = (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)))) ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term43 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term90 (x0 : real -> Prop) := exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 (sup x0))).
Definition term231 (x0 : real -> Prop) := @eq Prop ((x0 = (@EMPTY real)) \/ (exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))).
Definition term230 (x0 : real -> Prop) := @eq Prop ((x0 = (@EMPTY real)) \/ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0)).
Definition term232 (x0 : real -> Prop) (x1 : real -> real) := (x0 = (@EMPTY real)) \/ ((fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) x1).
Definition term412 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term470 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := forall y0 : real, ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ ((fun y1 : real => ((~ (@IN real y1 x2)) \/ (real_le y1 (sup x2))) /\ (((@IN real (x1 x2 y1) x2) /\ (~ (real_le (x1 x2 y1) y1))) \/ (real_le (sup x2) y1))) y0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term728 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := (~ ((~ (x1 = x3)) \/ ((~ (x0 = x2)) \/ (~ (@IN real x0 x1))))) -> @IN real x2 x3.
Definition term125 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1))) y0.
Definition term294 (x0 : real -> Prop) := (exists y0 : real -> real, (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ (exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))).
Definition term60 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0.
Definition term490 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := or (((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 x2) x1)) /\ ((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 x2) x2)))).
Definition term433 (x0 : real -> Prop) := and (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) y0).
Definition term396 := and (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0).
Definition term374 (x0 : real) := and (forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0).
Definition term138 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term11 (x0 : Prop) := (~ x0) -> False.
Definition term475 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := @eq Prop (((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (forall y0 : real, ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0)))).
Definition term474 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := @eq Prop (((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (forall y0 : real, (fun y1 : real => ((~ (@IN real y1 x2)) \/ (real_le y1 (sup x2))) /\ (((@IN real (x1 x2 y1) x2) /\ (~ (real_le (x1 x2 y1) y1))) \/ (real_le (sup x2) y1))) y0)).
Definition term48 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le y0 x1.
Definition term238 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term712 (x0 : real) (x1 : real) := imp (~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1)))).
Definition term158 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term84 (x0 : real -> Prop) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)).
Definition term73 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x1 x0)) \/ (real_le x1 x2).
Definition term351 (x0 : real) := fun y0 : real => (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term506 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) /\ ((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1)))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term13 (x0 : real -> Prop) := (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> False.
Definition term186 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1).
Definition term607 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ~ (~ (real_le (x0 x1 x2) x2)).
Definition term75 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term471 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))) x2.
Definition term380 := fun y0 : real => (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term649 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (real_le (x0 x2 x3) x3)) \/ ((x2 = (@EMPTY real)) \/ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3))).
Definition term669 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (~ (real_le (x0 x2 x1) x1)) -> ~ (@IN real (x0 x2 x1) x2).
Definition term284 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)) x1.
Definition term227 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) x1.
Definition term316 (x0 : real -> Prop) := exists y0 : real -> real, ((x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))).
Definition term121 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term41 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term106 (x0 : real -> Prop) := ~ (@IN real (sup x0) x0).
Definition term31 (x0 : real -> Prop) := imp ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))).
Definition term191 (x0 : real -> Prop) := or (~ ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0))).
Definition term289 (x0 : real -> Prop) (x1 : real -> real) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ ((fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)) x1).
Definition term754 := forall y0 : real -> Prop, ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (@IN real (sup y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)).
Definition term66 := forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1).
Definition term280 (x0 : Prop) (x1 : type1028) := x0 /\ (exists y0 : real -> real, x1 y0).
Definition term714 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (real_le x1 x0)) -> x0 = x1.
Definition term105 (x0 : real -> Prop) := exists y0 : real, (~ (@IN real (sup x0) x0)) \/ ((fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 (sup x0)))) y0).
Definition term401 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term565 (x0 : real) (x1 : real -> Prop) := ~ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1))).
Definition term32 (x0 : real -> Prop) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term87 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => (@IN real y0 x0) -> real_le y0 (sup x0)) x1).
Definition term285 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0.
Definition term228 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0.
Definition term334 (x0 : type1021) (x1 : real -> Prop) := ((x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term313 (x0 : real -> real) (x1 : real -> Prop) := ((x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0)))) \/ ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term194 (x0 : real -> Prop) := ((x0 = (@EMPTY real)) \/ (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)))) \/ ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0))).
Definition term408 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)).
Definition term218 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0)).
Definition term501 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)).
Definition term104 (x0 : real -> Prop) := (~ (@IN real (sup x0) x0)) \/ (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 (sup x0)))) y0).
Definition term315 (x0 : real -> Prop) := fun y0 : real -> real => ((x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))).
Definition term558 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term663 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((~ (x2 = (@EMPTY real))) /\ ((real_le (x1 x2 x0) x0) /\ (~ (real_le (sup x2) x3)))) -> ~ (real_le (x1 x2 x3) x3).
Definition term593 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))))).
Definition term727 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((@IN real x1 x0) \/ ((~ (x3 = x0)) \/ ((~ (x2 = x1)) \/ (~ (@IN real x2 x3))))).
Definition term552 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (@IN real (x0 x3 x1) x3) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term428 (x0 : type1021) (x1 : real -> Prop) := (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) y0) /\ (forall y0 : real, (fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0).
Definition term383 := (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term360 (x0 : real) := (forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term243 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ((fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0) \/ (real_le (sup x0) x1).
Definition term293 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)).
Definition term266 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y0 y1.
Definition term209 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1.
Definition term413 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (forall y0 : real, x1 y0).
Definition term448 (x0 : type1021) (x1 : real -> Prop) := @eq Prop (((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))) = (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)))).
Definition term516 (x0 : type1021) := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0)))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))))) /\ (((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2)))) /\ ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))))).
Definition term484 (x0 : type1021) := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, ((y0 = (@EMPTY real)) \/ ((@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1)))) \/ (((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (((@IN real (x0 y0 y2) y0) /\ (~ (real_le (x0 y0 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term583 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := real_le (x0 x1 x2) x2.
Definition term749 (x0 : real -> Prop) := (@IN real (sup x0) x0) -> False.
Definition term502 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))).
Definition term240 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) \/ x1.
Definition term686 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := ~ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3))).
Definition term655 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := ~ ((x2 = (@EMPTY real)) \/ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3))).
Definition term137 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term698 (x0 : real -> Prop) (x1 : real) := (~ (real_le (sup x0) x1)) -> real_le (sup x0) x1.
Definition term347 (x0 : real) (x1 : real) := ((~ (real_le x0 x1)) \/ (~ (real_le x1 x0))) \/ (x0 = x1).
Definition term515 (x0 : type1021) := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0)))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))))) /\ (((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2)))) /\ ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))))).
Definition term483 (x0 : type1021) := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, ((y0 = (@EMPTY real)) \/ ((@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1)))) \/ (((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (((@IN real (x0 y0 y2) y0) /\ (~ (real_le (x0 y0 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term640 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := ((~ (x2 = (@EMPTY real))) /\ ((~ (@IN real (x0 x2 x1) x2)) /\ (~ (real_le (sup x2) x1)))) -> @IN real (x0 x2 x1) x2.
Definition term216 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0)).
Definition term344 (x0 : real) (x1 : real) := or (~ ((real_le x1 x0) /\ (real_le x0 x1))).
Definition term524 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term544 (x0 : Prop) := (~ x0) -> x0.
Definition term346 (x0 : real) (x1 : real) := (~ ((real_le x0 x1) /\ (real_le x1 x0))) \/ (x0 = x1).
Definition term682 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (real_le (sup x3) x2) \/ ((~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3)).
Definition term645 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (real_le (sup x2) x3) \/ ((~ (real_le (x1 x2 x0) x0)) \/ (~ (real_le (x1 x2 x3) x3))).
Definition term455 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0) \/ (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term224 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 \/ (x1 y0).
Definition term590 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ (@IN real x0 x2)) \/ ((real_le x0 (sup x2)) \/ (~ (real_le (x1 x2 x3) x3))).
Definition term525 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))).
Definition term734 (x0 : real -> Prop) (x1 : real -> Prop) := and (x0 = x1).
Definition term678 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((real_le (sup x3) x2) \/ ((~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3))).
Definition term235 (x0 : real -> Prop) := fun y0 : real -> real => (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term699 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (x0 = x1).
Definition term135 (x0 : real -> Prop) := fun y0 : real => ((@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0))) /\ (exists y1 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y1 x0) /\ (~ (real_le y1 (sup x0))))).
Definition term398 := fun y0 : real => (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0.
Definition term393 := fun y0 : real => (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term52 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0.
Definition term570 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) /\ ((@IN real x0 x1) /\ (~ (real_le x0 (sup x1)))).
Definition term143 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (~ (@IN real (sup x0) x0)) \/ ((@IN real y0 x0) /\ (~ (real_le y0 (sup x0))))) x1.
Definition term63 (x0 : real -> Prop) := imp ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term562 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term111 (x0 : real -> Prop) := @eq Prop ((~ (@IN real (sup x0) x0)) \/ (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 (sup x0))))).
Definition term110 (x0 : real -> Prop) := @eq Prop ((~ (@IN real (sup x0) x0)) \/ (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 (sup x0)))) y0)).
Definition term671 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (@IN real (x0 x2 x3) x2) \/ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3)).
Definition term332 (x0 : type1021) (x1 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real -> real => ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2)))) x1 (x0 x1).
Definition term197 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term597 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)).
Definition term279 (x0 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)).
Definition term557 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (@IN real (x0 x3 x1) x3) \/ ((x3 = (@EMPTY real)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term629 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3)).
Definition term680 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (@IN real (x1 x2 x0) x2) \/ (~ (real_le (x1 x2 x3) x3)).
Definition term719 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := (@IN real x1 x0) \/ ((~ (x2 = x1)) \/ (~ (@IN real x2 x3))).
Definition term745 (x0 : real) (x1 : real -> Prop) := (x0 = (sup x1)) /\ (@IN real x0 x1).
Definition term339 := fun y0 : type1021 => forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y1 (y0 y1).
Definition term349 (x0 : real) (x1 : real) := (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))) /\ ((~ ((real_le x0 x1) /\ (real_le x1 x0))) \/ (x0 = x1)).
Definition term442 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((~ (@IN real x2 x1)) \/ (real_le x2 (sup x1))) /\ (((@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2))) \/ (real_le (sup x1) x2)).
Definition term430 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) x1.
Definition term245 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0.
Definition term145 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => (~ (@IN real (sup x0) x0)) \/ ((@IN real y1 x0) /\ (~ (real_le y1 (sup x0))))) y0.
Definition term126 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1))) y0.
Definition term109 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 (sup x0)))) y0.
Definition term636 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := imp ((~ (x2 = (@EMPTY real))) /\ ((~ (@IN real (x0 x2 x1) x2)) /\ (~ (real_le (sup x2) x3)))).
Definition term627 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := @eq Prop ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)))).
Definition term514 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1)))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))))) /\ (((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1)))) /\ ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))))).
Definition term482 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term400 := forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1).
Definition term395 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1)).
Definition term354 := forall y0 : real, forall y1 : real, (((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term45 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term21 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term183 (x0 : real -> Prop) (x1 : real) := or (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)).
Definition term124 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0))) x1.
Definition term341 := exists y0 : type1021, forall y1 : real -> Prop, ((y1 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y0 y1 y2) y1) /\ (~ (real_le (y0 y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y1)) \/ (real_le y2 (sup y1))) /\ (forall y2 : real, ((@IN real (y0 y1 y2) y1) /\ (~ (real_le (y0 y1 y2) y2))) \/ (real_le (sup y1) y2))).
Definition term322 := exists y0 : type1021, forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y1 (y0 y1).
Definition term320 (x0 : type1017) := exists y0 : type1021, forall y1 : real -> Prop, x0 y1 (y0 y1).
Definition term278 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1).
Definition term259 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y1 (y0 y1).
Definition term221 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)).
Definition term202 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y1 (y0 y1).
Definition term200 (x0 : type1626) := exists y0 : real -> real, forall y1 : real, x0 y1 (y0 y1).
Definition term445 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)).
Definition term352 (x0 : real) := forall y0 : real, (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term462 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := or ((fun y0 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) x2).
Definition term249 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1))) x2).
Definition term154 (x0 : real -> Prop) := exists y0 : real, exists y1 : real, ((@IN real y0 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y0))) /\ ((~ (@IN real (sup x0) x0)) \/ ((@IN real y1 x0) /\ (~ (real_le y1 (sup x0))))).
Definition term166 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term356 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term23 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term427 (x0 : type1021) (x1 : real -> Prop) := or (forall y0 : real, (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))).
Definition term140 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term326 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => ((x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)))) x1.
Definition term450 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term246 (x0 : real -> Prop) (x1 : real) := or (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0).
Definition term540 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := (x3 = x1) -> (~ (x2 = x0)) \/ ((@IN real x0 x1) \/ (~ (@IN real x2 x3))).
Definition term422 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (x1 = (@EMPTY real)) \/ ((fun y0 : real => (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) x2).
Definition term310 (x0 : real -> Prop) (x1 : real -> real) := or ((fun y0 : real -> real => (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) x1).
Definition term576 (x0 : real) (x1 : real) (x2 : real -> Prop) := (real_le x1 x0) \/ (~ (@IN real x1 x2)).
Definition term456 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) x2.
Definition term532 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term272 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le (sup x0) y1)) y0 (x1 y0).
Definition term215 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) y0 (x1 y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term214 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@IN real (x1 x2) x0) /\ (~ (real_le (x1 x2) x2)).
Definition term15 (x0 : real -> Prop) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term667 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (real_le (x0 x1 x2) x2) -> ~ (real_le (x0 x1 x2) x2).
Definition term601 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))))) -> real_le x2 (sup x3).
Definition term694 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((~ (x2 = (@EMPTY real))) /\ ((real_le (x1 x2 x0) x0) /\ (~ (@IN real (x1 x2 x3) x2)))) -> real_le (sup x2) x3.
Definition term706 (x0 : real) (x1 : real) := (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x0)))) -> x0 = x1.
Definition term131 (x0 : real -> Prop) (x1 : real) := and ((@IN real x1 x0) /\ (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1))).
Definition term549 (x0 : real) (x1 : real -> Prop) := (real_le x0 (sup x1)) -> ~ (real_le x0 (sup x1)).
Definition term564 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) /\ (~ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1)))).
Definition term637 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := ((~ (x3 = (@EMPTY real))) /\ ((~ (@IN real (x1 x3 x0) x3)) /\ (~ (real_le (sup x3) x2)))) -> @IN real (x1 x3 x2) x3.
Definition term573 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := ((~ (x3 = (@EMPTY real))) /\ ((@IN real x0 x3) /\ (~ (real_le x0 (sup x3))))) -> @IN real (x1 x3 x2) x3.
Definition term281 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 /\ (x1 y0).
Definition term705 (x0 : real) (x1 : real) := @eq Prop ((x1 = x0) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1)))).
Definition term695 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (real_le (x0 x2 x1) x1) /\ (~ (@IN real (x0 x2 x1) x2)).
Definition term159 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 x1) y0).
Definition term85 (x0 : real -> Prop) := exists y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 (sup x0)) y0).
Definition term117 (x0 : real -> Prop) := (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0))) /\ (exists y0 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y0 x0) /\ (~ (real_le y0 (sup x0))))).
Definition term743 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := imp ((x3 = x0) /\ ((x2 = x1) /\ (@IN real x2 x3))).
Definition term457 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0.
Definition term431 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) y0.
Definition term144 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => (~ (@IN real (sup x0) x0)) \/ ((@IN real y1 x0) /\ (~ (real_le y1 (sup x0))))) y0.
Definition term614 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((~ (x3 = (@EMPTY real))) /\ ((real_le (x0 x3 x1) x1) /\ (@IN real x2 x3))) -> real_le x2 (sup x3).
Definition term613 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := imp ((~ (x3 = (@EMPTY real))) /\ ((real_le (x0 x3 x1) x1) /\ (@IN real x2 x3))).
Definition term619 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (@IN real (x0 x2 x1) x2) -> ~ (@IN real (x0 x2 x1) x2).
Definition term113 (x0 : real) (x1 : real -> Prop) := (~ (@IN real (sup x1) x1)) \/ ((@IN real x0 x1) /\ (~ (real_le x0 (sup x1)))).
Definition term223 (x0 : Prop) (x1 : type1028) := x0 \/ (exists y0 : real -> real, x1 y0).
Definition term414 (x0 : Prop) (x1 : real -> Prop) := forall y0 : real, x0 \/ (x1 y0).
Definition term160 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le y0 x1) x2.
Definition term167 (x0 : real -> Prop) := ~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term269 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)) x2 (x1 x2).
Definition term212 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x2 (x1 x2).
Definition term12 (x0 : real -> Prop) := (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)).
Definition term449 (x0 : type1021) (x1 : real -> Prop) := (forall y0 : real, (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term654 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3)).
Definition term261 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)) x1.
Definition term517 (x0 : type1021) (x1 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, forall y2 : real, ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0)))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))))) /\ (((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((@IN real (x0 y0 y2) y0) \/ (real_le (sup y0) y2)))) /\ ((((y0 = (@EMPTY real)) \/ (@IN real (x0 y0 y1) y0)) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2))) /\ (((y0 = (@EMPTY real)) \/ (~ (real_le (x0 y0 y1) y1))) \/ ((~ (real_le (x0 y0 y2) y2)) \/ (real_le (sup y0) y2)))))) x1.
Definition term171 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) y0).
Definition term392 := @eq Prop (forall y0 : real, (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1))).
Definition term391 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0)).
Definition term370 (x0 : real) := @eq Prop (forall y0 : real, (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0))).
Definition term369 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0)).
Definition term421 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))).
Definition term420 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((x1 = (@EMPTY real)) \/ (forall y0 : real, (fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0)).
Definition term89 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 (sup x0))).
Definition term657 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := ~ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3)).
Definition term350 (x0 : real) (x1 : real) := (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))) /\ (((~ (real_le x0 x1)) \/ (~ (real_le x1 x0))) \/ (x0 = x1)).
Definition term79 (x0 : real) (x1 : real -> Prop) := ~ ((@IN real x0 x1) -> real_le x0 (sup x1)).
Definition term338 (x0 : type1021) := forall y0 : real -> Prop, ((y0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 (sup y0))) /\ (forall y1 : real, ((@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1))) \/ (real_le (sup y0) y1))).
Definition term196 := forall y0 : real -> Prop, ((y0 = (@EMPTY real)) \/ (forall y1 : real, exists y2 : real, (@IN real y2 y0) /\ (~ (real_le y2 y1)))) \/ ((forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 (sup y0))) /\ (forall y1 : real, (exists y2 : real, (@IN real y2 y0) /\ (~ (real_le y2 y1))) \/ (real_le (sup y0) y1))).
Definition term172 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term343 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_le x0 x1)).
Definition term492 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ (((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)) /\ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)))).
Definition term513 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1)))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))))) /\ (((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1)))) /\ ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))))).
Definition term481 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term353 := fun y0 : real => forall y1 : real, (((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term615 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (real_le (x0 x2 x1) x1) /\ (@IN real x1 x2).
Definition term129 (x0 : real -> Prop) := @eq Prop ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0))) /\ (exists y0 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y0 x0) /\ (~ (real_le y0 (sup x0)))))).
Definition term128 (x0 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1))) y0) /\ (exists y0 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y0 x0) /\ (~ (real_le y0 (sup x0)))))).
Definition term19 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term621 (x0 : real -> Prop) (x1 : real) := (real_le (sup x0) x1) -> ~ (real_le (sup x0) x1).
Definition term270 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x2))) \/ (real_le (sup x0) x2)) (x1 x2).
Definition term49 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term18 (x0 : real -> Prop) := ((((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> (((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term323 := fun y0 : real -> Prop => fun y1 : real -> real => ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term37 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term93 (x0 : real -> Prop) := (~ (@IN real (sup x0) x0)) \/ (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 (sup x0)))).
Definition term579 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (~ (@IN real x1 x0))) -> real_le x1 x2.
Definition term286 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0.
Definition term229 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0.
Definition term670 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ (real_le (x1 x2 x0) x0)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)).
Definition term321 := forall y0 : real -> Prop, exists y1 : real -> real, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y0 y1.
Definition term319 (x0 : type1017) := forall y0 : real -> Prop, exists y1 : real -> real, x0 y0 y1.
Definition term720 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term537 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := (x2 = x0) -> (@IN real x0 x1) \/ (~ (@IN real x2 x3)).
Definition term333 (x0 : type1021) (x1 : real -> Prop) := (fun y0 : real -> real => ((x1 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x1) /\ (~ (real_le (y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (forall y1 : real, ((@IN real (y0 y1) x1) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x1) y1)))) (x0 x1).
Definition term20 := ~ (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term665 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (~ (x1 = (@EMPTY real))) /\ ((real_le (x0 x1 x2) x2) /\ (~ (real_le (sup x1) x2))).
Definition term531 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((@IN real (x0 x3 x1) x3) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))).
Definition term600 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (real_le x2 (sup x3)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))).
Definition term241 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) \/ x1.
Definition term612 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := imp (~ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))))).
Definition term610 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (real_le (x0 x3 x1) x1) /\ (@IN real x2 x3).
Definition term744 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := ((x1 = x3) /\ ((x0 = x2) /\ (@IN real x0 x1))) -> @IN real x2 x3.
Definition term548 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term617 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := ((~ (x2 = (@EMPTY real))) /\ ((real_le (x0 x2 x1) x1) /\ (@IN real x1 x2))) -> real_le x1 (sup x2).
Definition term594 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := @eq Prop ((x2 = (@EMPTY real)) \/ ((real_le x0 (sup x2)) \/ ((~ (@IN real x0 x2)) \/ (~ (real_le (x1 x2 x3) x3))))).
Definition term362 (x0 : real) := fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0).
Definition term53 (x0 : real -> Prop) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0.
Definition term331 := @eq Prop (forall y0 : real -> Prop, exists y1 : real -> real, ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2)))).
Definition term330 := @eq Prop (forall y0 : real -> Prop, exists y1 : real -> real, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y0 y1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term410 (x0 : type1021) (x1 : real -> Prop) := or ((x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))).
Definition term311 (x0 : real -> Prop) (x1 : real -> real) := or ((x0 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0)))).
Definition term192 (x0 : real -> Prop) := or ((x0 = (@EMPTY real)) \/ (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)))).
Definition term535 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := ((@IN real x2 x3) = (@IN real x0 x1)) -> (@IN real x0 x1) \/ (~ (@IN real x2 x3)).
Definition term268 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)).
Definition term267 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y0 y1).
Definition term211 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))).
Definition term210 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1).
Definition term461 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)))).
Definition term460 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((forall y0 : real, (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0) \/ (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)))).
Definition term679 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3).
Definition term688 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := ~ ((~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3)).
Definition term681 (x0 : real -> Prop) (x1 : real) := or (real_le (sup x0) x1).
Definition term263 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1)) x2.
Definition term101 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term148 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((@IN real x0 x1) /\ (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 x0))) /\ ((fun y0 : real => (~ (@IN real (sup x1) x1)) \/ ((@IN real y0 x1) /\ (~ (real_le y0 (sup x1))))) x2).
Definition term494 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))).
Definition term77 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)).
Definition term71 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term72 (x0 : real -> Prop) := imp (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term584 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (~ (real_le (x0 x1 x2) x2)) -> real_le (x0 x1 x2) x2.
Definition term561 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term591 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (real_le x0 (sup x2)) \/ ((~ (@IN real x0 x2)) \/ (~ (real_le (x1 x2 x3) x3))).
Definition term405 (x0 : type1021) (x1 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)).
Definition term379 (x0 : real) := (forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term290 (x0 : real -> real) (x1 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le (sup x1) y0)).
Definition term190 (x0 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)).
Definition term58 (x0 : real -> Prop) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0).
Definition term282 (x0 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0).
Definition term61 (x0 : real -> Prop) := and (~ (x0 = (@EMPTY real))).
Definition term746 (x0 : real) (x1 : real -> Prop) := (x1 = x1) /\ ((x0 = (sup x1)) /\ (@IN real x0 x1)).
Definition term702 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ ((x1 = x0) \/ (~ (real_le x0 x1))).
Definition term642 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := or (~ (real_le (x0 x1 x2) x2)).
Definition term299 (x0 : real -> Prop) := (exists y0 : real -> real, (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0) \/ (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0).
Definition term500 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 x2) x2)).
Definition term550 (x0 : real) (x1 : real -> Prop) := (real_le x0 (sup x1)) \/ (~ (@IN real x0 x1)).
Definition term100 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term133 (x0 : real) (x1 : real -> Prop) := ((@IN real x0 x1) /\ (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 x0))) /\ (exists y0 : real, (~ (@IN real (sup x1) x1)) \/ ((@IN real y0 x1) /\ (~ (real_le y0 (sup x1))))).
Definition term236 (x0 : real -> Prop) := exists y0 : real -> real, (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term523 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term452 (x0 : real -> Prop) (x1 : Prop) := (forall y0 : real, x0 y0) \/ x1.
Definition term262 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0)) x1 x2.
Definition term205 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x1 x2.
Definition term153 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, ((@IN real y0 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y0))) /\ ((~ (@IN real (sup x0) x0)) \/ ((@IN real y1 x0) /\ (~ (real_le y1 (sup x0))))).
Definition term165 (x0 : real -> Prop) := ~ (ex x0).
Definition term459 (x0 : type1021) (x1 : real -> Prop) := or (forall y0 : real, (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0).
Definition term543 (x0 : real -> Prop) := ~ (x0 = x0).
Definition term234 (x0 : real -> Prop) := fun y0 : real -> real => (x0 = (@EMPTY real)) \/ ((fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term424 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (x1 = (@EMPTY real)) \/ ((fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0).
Definition term361 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0)).
Definition term329 := fun y0 : real -> Prop => exists y1 : real -> real, (fun y2 : real -> Prop => fun y3 : real -> real => ((y2 = (@EMPTY real)) \/ (forall y4 : real, (@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4)))) \/ ((forall y4 : real, (~ (@IN real y4 y2)) \/ (real_le y4 (sup y2))) /\ (forall y4 : real, ((@IN real (y3 y4) y2) /\ (~ (real_le (y3 y4) y4))) \/ (real_le (sup y2) y4)))) y0 y1.
Definition term258 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y0 y1.
Definition term257 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term201 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1.
Definition term199 (x0 : type1626) := forall y0 : real, exists y1 : real, x0 y0 y1.
Definition term173 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term132 (x0 : real) (x1 : real -> Prop) := ((fun y0 : real => (@IN real y0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 y0))) x0) /\ (exists y0 : real, (~ (@IN real (sup x1) x1)) \/ ((@IN real y0 x1) /\ (~ (real_le y0 (sup x1))))).
Definition term618 (x0 : real) (x1 : real -> Prop) := (~ (real_le x0 (sup x1))) -> real_le x0 (sup x1).
Definition term638 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (~ (@IN real (x0 x1 x2) x1)) /\ (~ (real_le (sup x1) x2)).
Definition term371 (x0 : real) := fun y0 : real => (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term509 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := and ((((x3 = (@EMPTY real)) \/ (@IN real (x0 x3 x1) x3)) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3)))) /\ (((x3 = (@EMPTY real)) \/ (~ (real_le (x0 x3 x1) x1))) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))))).
Definition term69 (x0 : real) (x1 : real -> Prop) := and (@IN real x0 x1).
Definition term348 (x0 : real) (x1 : real) := and (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))).
Definition term225 (x0 : real -> Prop) := (x0 = (@EMPTY real)) \/ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term297 (x0 : type1028) (x1 : type1028) := (exists y0 : real -> real, x0 y0) \/ (exists y0 : real -> real, x1 y0).
Definition term366 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)) x1.
Definition term328 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> Prop => fun y2 : real -> real => ((y1 = (@EMPTY real)) \/ (forall y3 : real, (@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3)))) \/ ((forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y3 (sup y1))) /\ (forall y3 : real, ((@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3))) \/ (real_le (sup y1) y3)))) x0 y0.
Definition term179 (x0 : real -> Prop) := ~ (x0 = (@EMPTY real)).
Definition term55 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) -> real_le y0 (sup x0).
Definition term696 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (~ (x2 = (@EMPTY real))) /\ ((real_le (x0 x2 x1) x1) /\ (~ (@IN real (x0 x2 x1) x2))).
Definition term660 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (x2 = (@EMPTY real))) /\ ((real_le (x0 x2 x1) x1) /\ (~ (real_le (sup x2) x3))).
Definition term176 (x0 : real -> Prop) := (~ (~ (x0 = (@EMPTY real)))) \/ (~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term54 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) -> real_le x0 (sup x1).
Definition term46 (x0 : real -> Prop) (x1 : real) := real_le (sup x0) x1.
Definition term477 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2))) /\ (((@IN real (x1 x2 x3) x2) /\ (~ (real_le (x1 x2 x3) x3))) \/ (real_le (sup x2) x3))).
Definition term312 (x0 : real -> Prop) (x1 : real -> real) := ((fun y0 : real -> real => (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) x1) \/ ((fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))) x1).
Definition term385 := fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1).
Definition term59 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0.
Definition term44 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term40 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term253 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0) \/ (real_le (sup x0) x1).
Definition term521 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)).
Definition term213 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x2))) (x1 x2).
Definition term83 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term740 (x0 : real) (x1 : real) (x2 : real -> Prop) := (x1 = x0) /\ (@IN real x1 x2).
Definition term357 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term161 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (@IN real y0 x0) -> real_le y0 x1) x2).
Definition term25 := imp (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)).
Definition term653 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ ((x2 = (@EMPTY real)) \/ ((~ (real_le (x1 x2 x0) x0)) \/ (real_le (sup x2) x3)))) -> ~ (real_le (x1 x2 x3) x3).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term716 (x0 : real) (x1 : real -> Prop) := ((real_le x0 (sup x1)) /\ (real_le (sup x1) x0)) -> x0 = (sup x1).
Definition term388 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)) x0.
Definition term386 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0.
Definition term239 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term673 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (@IN real (x1 x2 x0) x2) \/ ((real_le (sup x2) x0) \/ (~ (real_le (x1 x2 x3) x3))).
Definition term581 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term102 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term255 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ((@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1).
Definition term180 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) \/ (real_le x0 (sup x1)).
Definition term193 (x0 : real -> Prop) := (~ ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0))) \/ ((forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0)).
Definition term554 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((@IN real (x0 x3 x1) x3) \/ ((real_le x2 (sup x3)) \/ (~ (@IN real x2 x3)))).
Definition term409 (x0 : type1021) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))).
Definition term464 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := ((fun y0 : real => (x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0)))) x0) \/ (forall y0 : real, ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))).
Definition term730 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := ~ ((~ (x3 = x0)) \/ ((~ (x2 = x1)) \/ (~ (@IN real x2 x3)))).
Definition term616 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (~ (x2 = (@EMPTY real))) /\ ((real_le (x0 x2 x1) x1) /\ (@IN real x1 x2)).
Definition term568 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term177 (x0 : real -> Prop) := (x0 = (@EMPTY real)) \/ (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))).
Definition term588 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (real_le x0 (sup x2)) \/ (~ (real_le (x1 x2 x3) x3)).
Definition term345 (x0 : real) (x1 : real) := or ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term480 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := forall y0 : real, ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))).
Definition term473 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (fun y1 : real => ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))) y0.
Definition term458 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0.
Definition term436 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0.
Definition term432 (x0 : real -> Prop) := forall y0 : real, (fun y1 : real => (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) y0.
Definition term419 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0.
Definition term377 (x0 : real) := forall y0 : real, (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0.
Definition term372 (x0 : real) := forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term95 (x0 : real -> Prop) := @IN real (sup x0) x0.
Definition term555 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((x3 = (@EMPTY real)) \/ ((@IN real (x0 x3 x1) x3) \/ ((~ (@IN real x2 x3)) \/ (real_le x2 (sup x3))))).
Definition term42 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term34 := fun y0 : real -> Prop => ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (~ ((exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (@IN real (sup y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)))) -> (forall y1 : real -> Prop, ((~ (y1 = (@EMPTY real))) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2)) -> (forall y2 : real, (@IN real y2 y1) -> real_le y2 (sup y1)) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> real_le (sup y1) y2)) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> ~ (forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) = (y1 = y2)).
Definition term33 := fun y0 : real -> Prop => ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (~ ((exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (@IN real (sup y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)))) -> (forall y1 : real -> Prop, ((~ (y1 = (@EMPTY real))) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2)) -> (forall y2 : real, (@IN real y2 y1) -> real_le y2 (sup y1)) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> real_le (sup y1) y2)) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) = (y1 = y2)) -> False.
Definition term639 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (~ (x1 = (@EMPTY real))) /\ ((~ (@IN real (x0 x1 x2) x1)) /\ (~ (real_le (sup x1) x2))).
Definition term634 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (x2 = (@EMPTY real))) /\ ((~ (@IN real (x0 x2 x1) x2)) /\ (~ (real_le (sup x2) x3))).
Definition term479 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := fun y0 : real => ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))).
Definition term141 (x0 : real) (x1 : real -> Prop) := ((@IN real x0 x1) /\ (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 x0))) /\ (exists y0 : real, (fun y1 : real => (~ (@IN real (sup x1) x1)) \/ ((@IN real y1 x1) /\ (~ (real_le y1 (sup x1))))) y0).
Definition term94 (x0 : real -> Prop) := ~ ((@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0))).
Definition term47 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) -> real_le x1 x2.
Definition term298 (x0 : type1028) (x1 : type1028) := exists y0 : real -> real, (x0 y0) \/ (x1 y0).
Definition term67 (x0 : real -> Prop) := and (@IN real (sup x0) x0).
Definition term390 := fun y0 : real => ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term651 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3).
Definition term451 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term693 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := imp ((~ (x3 = (@EMPTY real))) /\ ((real_le (x1 x3 x0) x0) /\ (~ (@IN real (x1 x3 x2) x3)))).
Definition term662 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := imp ((~ (x2 = (@EMPTY real))) /\ ((real_le (x0 x2 x1) x1) /\ (~ (real_le (sup x2) x3)))).
Definition term572 (x0 : real) (x1 : real -> Prop) := imp ((~ (x1 = (@EMPTY real))) /\ ((@IN real x0 x1) /\ (~ (real_le x0 (sup x1))))).
Definition term677 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (real_le (sup x3) x2) \/ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3))).
Definition term575 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := ~ (@IN real (x0 x2 x1) x2).
Definition term753 (x0 : real -> Prop) := ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)).
Definition term447 (x0 : type1021) (x1 : real -> Prop) := @eq Prop ((fun y0 : Prop => y0 = (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)))) ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)))).
Definition term65 := fun y0 : real -> Prop => ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1).
Definition term51 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1) -> real_le (sup x0) x1.
Definition term596 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((real_le x2 (sup x3)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)))).
Definition term646 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((real_le (sup x2) x3) \/ ((~ (real_le (x1 x2 x0) x0)) \/ (~ (real_le (x1 x2 x3) x3)))).
Definition term703 (x0 : real) (x1 : real) := (x1 = x0) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term226 (x0 : real -> Prop) := exists y0 : real -> real, (x0 = (@EMPTY real)) \/ ((fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term336 (x0 : type1021) := fun y0 : real -> Prop => ((y0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1)))) \/ ((forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 (sup y0))) /\ (forall y1 : real, ((@IN real (x0 y0 y1) y0) /\ (~ (real_le (x0 y0 y1) y1))) \/ (real_le (sup y0) y1))).
Definition term195 := fun y0 : real -> Prop => ((y0 = (@EMPTY real)) \/ (forall y1 : real, exists y2 : real, (@IN real y2 y0) /\ (~ (real_le y2 y1)))) \/ ((forall y1 : real, (~ (@IN real y1 y0)) \/ (real_le y1 (sup y0))) /\ (forall y1 : real, (exists y2 : real, (@IN real y2 y0) /\ (~ (real_le y2 y1))) \/ (real_le (sup y0) y1))).
Definition term519 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (fun y0 : real => ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2)))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))))) /\ (((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0)))))) x3.
Definition term38 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term624 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3).
Definition term526 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ ((~ (real_le x1 x0)) \/ (x0 = x1)).
Definition term416 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (x1 = (@EMPTY real)) \/ ((fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0).
Definition term254 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1).
Definition term147 (x0 : real) (x1 : real -> Prop) := @eq Prop (((@IN real x0 x1) /\ (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 x0))) /\ (exists y0 : real, (~ (@IN real (sup x1) x1)) \/ ((@IN real y0 x1) /\ (~ (real_le y0 (sup x1)))))).
Definition term146 (x0 : real) (x1 : real -> Prop) := @eq Prop (((@IN real x0 x1) /\ (forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le y0 x0))) /\ (exists y0 : real, (fun y1 : real => (~ (@IN real (sup x1) x1)) \/ ((@IN real y1 x1) /\ (~ (real_le y1 (sup x1))))) y0)).
Definition term441 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((fun y0 : real => (~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) x2) /\ ((fun y0 : real => ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)) x2).
Definition term701 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term367 (x0 : real) (x1 : real) := ((fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1) /\ ((fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)) x1).
Definition term503 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := and ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))).
Definition term169 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) x1.
Definition term251 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((fun y0 : real => (@IN real y0 x1) /\ (~ (real_le y0 x2))) x0) \/ (real_le (sup x1) x2).
Definition term182 (x0 : real -> Prop) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0)).
Definition term738 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term733 (x0 : real -> Prop) (x1 : real -> Prop) := and (~ (~ (x0 = x1))).
Definition term710 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term569 (x0 : real) (x1 : real -> Prop) := and (~ (~ (@IN real x0 x1))).
Definition term283 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ ((fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0).
Definition term700 (x0 : real) (x1 : real) := (x1 = x0) \/ (~ (real_le x0 x1)).
Definition term691 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (~ (x3 = (@EMPTY real))) /\ ((real_le (x1 x3 x0) x0) /\ (~ (@IN real (x1 x3 x2) x3))).
Definition term672 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (real_le (sup x2) x0) \/ (~ (real_le (x1 x2 x3) x3)).
Definition term86 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le y0 (sup x0)) x1.
Definition term592 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((real_le x0 (sup x2)) \/ ((~ (@IN real x0 x2)) \/ (~ (real_le (x1 x2 x3) x3)))).
Definition term264 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le (sup x0) y1)) x1 y0.
Definition term207 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) x1 y0.
Definition term658 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (~ (real_le (x0 x2 x1) x1))) /\ (~ (real_le (sup x2) x3)).
Definition term723 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := (@IN real x1 x0) \/ ((~ (x3 = x0)) \/ ((~ (x2 = x1)) \/ (~ (@IN real x2 x3)))).
Definition term454 (x0 : type1021) (x1 : real -> Prop) := (forall y0 : real, (fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0) \/ (forall y0 : real, ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0))).
Definition term487 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ~ (real_le (x0 x1 x2) x2).
Definition term274 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le (sup x0) y1)) y0 (x1 y0).
Definition term217 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) y0 (x1 y0).
Definition term440 (x0 : real) (x1 : real -> Prop) := and ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1))).
Definition term722 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (x3 = x0)) \/ ((@IN real x1 x0) \/ ((~ (x2 = x1)) \/ (~ (@IN real x2 x3)))).
Definition term598 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ (@IN real x0 x2)) \/ (~ (real_le (x1 x2 x3) x3)).
Definition term534 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term468 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term423 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2))).
Definition term68 (x0 : real -> Prop) := (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)).
Definition term574 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (~ (@IN real (x0 x2 x1) x2)) -> @IN real (x0 x2 x1) x2.
Definition term292 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)).
Definition term152 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((@IN real x0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x0))) /\ ((~ (@IN real (sup x1) x1)) \/ ((@IN real y0 x1) /\ (~ (real_le y0 (sup x1))))).
Definition term498 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))).
Definition term713 (x0 : real) (x1 : real) := imp ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term603 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ~ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)))).
Definition term337 (x0 : type1021) := forall y0 : real -> Prop, (fun y1 : real -> Prop => fun y2 : real -> real => ((y1 = (@EMPTY real)) \/ (forall y3 : real, (@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3)))) \/ ((forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y3 (sup y1))) /\ (forall y3 : real, ((@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3))) \/ (real_le (sup y1) y3)))) y0 (x0 y0).
Definition term103 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term27 := (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term553 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (@IN real (x0 x3 x1) x3) \/ ((real_le x2 (sup x3)) \/ (~ (@IN real x2 x3))).
Definition term120 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term518 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => forall y1 : real, ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1)))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))))) /\ (((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((@IN real (x0 x1 y1) x1) \/ (real_le (sup x1) y1)))) /\ ((((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 y0) x1)) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1))) /\ (((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 y0) y0))) \/ ((~ (real_le (x0 x1 y1) y1)) \/ (real_le (sup x1) y1)))))) x2.
Definition term620 (x0 : real -> Prop) (x1 : real) := ~ (real_le (sup x0) x1).
Definition term718 (x0 : real) (x1 : real -> Prop) := ~ (x0 = (sup x1)).
Definition term496 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (~ (real_le (x0 x1 x2) x2)) \/ (real_le (sup x1) x2).
Definition term504 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := and ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)))).
Definition term256 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term683 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (real_le (sup x2) x0) \/ ((@IN real (x1 x2 x0) x2) \/ (~ (real_le (x1 x2 x3) x3))).
Definition term623 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((@IN real (x0 x2 x3) x2) \/ ((@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3))).
Definition term529 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))).
Definition term586 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (@IN real x2 x3)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (real_le x2 (sup x3))).
Definition term650 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((~ (real_le (x0 x2 x3) x3)) \/ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3))).
Definition term530 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((~ (real_le (x1 x2 x0) x0)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))).
Definition term528 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((~ (real_le (x1 x2 x0) x0)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))).
Definition term444 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((~ (@IN real y0 x1)) \/ (real_le y0 (sup x1))) /\ (((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0)).
Definition term170 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) x1).
Definition term277 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1).
Definition term276 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => ((@IN real y3 x0) /\ (~ (real_le y3 y2))) \/ (real_le (sup x0) y2)) y1 (y0 y1).
Definition term220 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)).
Definition term219 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y1 (y0 y1).
Definition term578 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((real_le x1 x0) \/ (~ (@IN real x1 x2))).
Definition term622 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (@IN real (x0 x2 x3) x2) \/ ((x2 = (@EMPTY real)) \/ ((@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3))).
Definition term628 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (~ ((x3 = (@EMPTY real)) \/ ((@IN real (x1 x3 x0) x3) \/ (real_le (sup x3) x2)))) -> @IN real (x1 x3 x2) x3.
Definition term559 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (~ ((x3 = (@EMPTY real)) \/ ((~ (@IN real x0 x3)) \/ (real_le x0 (sup x3))))) -> @IN real (x1 x3 x2) x3.
Definition term98 (x0 : real -> Prop) := (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) /\ (~ ((@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))).
Definition term604 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (x3 = (@EMPTY real))) /\ (~ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3)))).
Definition term676 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := @eq Prop ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) \/ ((real_le (sup x2) x0) \/ (~ (real_le (x1 x2 x3) x3))))).
Definition term648 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := @eq Prop ((x2 = (@EMPTY real)) \/ ((real_le (sup x2) x3) \/ ((~ (real_le (x1 x2 x0) x0)) \/ (~ (real_le (x1 x2 x3) x3))))).
Definition term556 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := @eq Prop ((x3 = (@EMPTY real)) \/ ((@IN real (x0 x3 x1) x3) \/ ((real_le x2 (sup x3)) \/ (~ (@IN real x2 x3))))).
Definition term304 (x0 : real -> Prop) := or (exists y0 : real -> real, (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0).
Definition term527 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term684 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ ((x2 = (@EMPTY real)) \/ ((~ (real_le (x1 x2 x0) x0)) \/ (@IN real (x1 x2 x3) x2)))) -> real_le (sup x2) x3.
Definition term164 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1)).
Definition term381 := forall y0 : real, (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term187 (x0 : real -> Prop) := fun y0 : real => (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term729 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (x3 = x0)) \/ ((~ (x2 = x1)) \/ (~ (@IN real x2 x3))).
Definition term735 (x0 : real) (x1 : real) (x2 : real -> Prop) := ~ ((~ (x1 = x0)) \/ (~ (@IN real x1 x2))).
Definition term707 (x0 : real) (x1 : real) := ~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term605 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := ~ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))).
Definition term491 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ (((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2))) /\ (((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)) /\ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)))).
Definition term726 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := @eq Prop ((~ (x3 = x1)) \/ ((~ (x2 = x0)) \/ ((@IN real x0 x1) \/ (~ (@IN real x2 x3))))).
Definition term426 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))).
Definition term542 (x0 : real -> Prop) := (~ (x0 = x0)) -> x0 = x0.
Definition term499 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := (x2 = (@EMPTY real)) \/ (@IN real (x0 x2 x1) x2).
Definition term582 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (@IN real (x0 x1 x2) x1) -> real_le (x0 x1 x2) x2.
Definition term127 (x0 : real -> Prop) := and (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1))) y0).
Definition term668 (x0 : real) (x1 : real) (x2 : real -> Prop) := (~ (real_le x1 x0)) -> ~ (@IN real x1 x2).
Definition term472 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))) y0.
Definition term9 (x0 : real -> Prop) := (@FINITE real x0) /\ (~ (x0 = (@EMPTY real))).
Definition term399 := forall y0 : real, (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0.
Definition term394 := forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term541 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := (~ (x3 = x1)) \/ ((~ (x2 = x0)) \/ ((@IN real x0 x1) \/ (~ (@IN real x2 x3)))).
Definition term305 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))) x1.
Definition term685 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3)).
Definition term739 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term203 (x0 : real -> Prop) := fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term690 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := (real_le (x1 x3 x0) x0) /\ (~ (@IN real (x1 x3 x2) x3)).
Definition term389 (x0 : real) := ((fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0) /\ ((fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)) x0).
Definition term300 (x0 : real -> Prop) := exists y0 : real -> real, ((fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0) \/ ((fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0).
Definition term24 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term711 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term538 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term731 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (~ (x3 = x0))) /\ (~ ((~ (x2 = x1)) \/ (~ (@IN real x2 x3)))).
Definition term123 (x0 : real -> Prop) := exists y0 : real, ((fun y1 : real => (@IN real y1 x0) /\ (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 y1))) y0) /\ (exists y1 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y1 x0) /\ (~ (real_le y1 (sup x0))))).
Definition term136 (x0 : real -> Prop) := exists y0 : real, ((@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0))) /\ (exists y1 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y1 x0) /\ (~ (real_le y1 (sup x0))))).
Definition term443 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) y0) /\ ((fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0).
Definition term368 (x0 : real) := fun y0 : real => ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term435 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0.
Definition term376 (x0 : real) := fun y0 : real => (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0.
Definition term488 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((~ (@IN real x2 x1)) \/ (real_le x2 (sup x1))) /\ (((@IN real (x0 x1 x2) x1) \/ (real_le (sup x1) x2)) /\ ((~ (real_le (x0 x1 x2) x2)) \/ (real_le (sup x1) x2))).
Definition term571 (x0 : real) (x1 : real -> Prop) := imp (~ ((x1 = (@EMPTY real)) \/ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1))))).
Definition term478 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := fun y0 : real => ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ ((fun y1 : real => ((~ (@IN real y1 x2)) \/ (real_le y1 (sup x2))) /\ (((@IN real (x1 x2 y1) x2) /\ (~ (real_le (x1 x2 y1) y1))) \/ (real_le (sup x2) y1))) y0).
Definition term512 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := forall y0 : real, ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2)))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))))) /\ (((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))))).
Definition term206 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1))) x2.
Definition term633 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (@IN real (x0 x2 x1) x2)) /\ (~ (real_le (sup x2) x3)).
Definition term168 (x0 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) y0).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term50 (x0 : real -> Prop) (x1 : real) := imp (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term335 (x0 : type1021) := fun y0 : real -> Prop => (fun y1 : real -> Prop => fun y2 : real -> real => ((y1 = (@EMPTY real)) \/ (forall y3 : real, (@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3)))) \/ ((forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y3 (sup y1))) /\ (forall y3 : real, ((@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3))) \/ (real_le (sup y1) y3)))) y0 (x0 y0).
Definition term99 (x0 : real -> Prop) := (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0))) /\ ((~ (@IN real (sup x0) x0)) \/ (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 (sup x0))))).
Definition term547 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) -> @IN real x0 x1.
Definition term162 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 x1) y0).
Definition term88 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 (sup x0)) y0).
Definition term747 (x0 : real) (x1 : real -> Prop) := ((x1 = x1) /\ ((x0 = (sup x1)) /\ (@IN real x0 x1))) -> @IN real (sup x1) x1.
Definition term626 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (@IN real (x1 x2 x0) x2) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)).
Definition term625 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := (@IN real (x0 x2 x3) x2) \/ ((@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3)).
Definition term327 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> Prop => fun y2 : real -> real => ((y1 = (@EMPTY real)) \/ (forall y3 : real, (@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3)))) \/ ((forall y3 : real, (~ (@IN real y3 y1)) \/ (real_le y3 (sup y1))) /\ (forall y3 : real, ((@IN real (y2 y3) y1) /\ (~ (real_le (y2 y3) y3))) \/ (real_le (sup y1) y3)))) x0 y0.
Definition term406 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2)).
Definition term363 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1.
Definition term674 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) \/ ((real_le (sup x2) x0) \/ (~ (real_le (x1 x2 x3) x3)))).
Definition term522 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)).
Definition term56 (x0 : real -> Prop) := forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0).
Definition term358 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term325 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> Prop => fun y1 : real -> real => ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2)))) x0 x1.
Definition term704 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x0 x1)) \/ ((~ (real_le x1 x0)) \/ (x0 = x1))).
Definition term157 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) /\ (~ (real_le x1 x2)).
Definition term748 (x0 : real -> Prop) := (~ (@IN real (sup x0) x0)) -> @IN real (sup x0) x0.
Definition term643 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (~ (real_le (x1 x2 x0) x0)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3)).
Definition term560 (x0 : real) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1))).
Definition term174 (x0 : real -> Prop) := or (~ (~ (x0 = (@EMPTY real)))).
Definition term725 (x0 : real) (x1 : real) (x2 : real -> Prop) := (~ (x1 = x0)) \/ (~ (@IN real x1 x2)).
Definition term188 (x0 : real -> Prop) := forall y0 : real, (exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term511 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := fun y0 : real => ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2)))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))))) /\ (((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 y0) x2) \/ (real_le (sup x2) y0)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 y0) y0)) \/ (real_le (sup x2) y0))))).
Definition term288 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (exists y0 : real -> real, forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1))).
Definition term287 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) /\ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2)) y0)).
Definition term355 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term717 (x0 : real) (x1 : real -> Prop) := (~ (x0 = (sup x1))) -> x0 = (sup x1).
Definition term91 (x0 : real -> Prop) := or (~ (@IN real (sup x0) x0)).
Definition term563 (x0 : real) (x1 : real -> Prop) := ~ ((x1 = (@EMPTY real)) \/ ((~ (@IN real x0 x1)) \/ (real_le x0 (sup x1)))).
Definition term489 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((x1 = (@EMPTY real)) \/ (@IN real (x0 x1 x2) x1)) /\ ((x1 = (@EMPTY real)) \/ (~ (real_le (x0 x1 x2) x2))).
Definition term78 (x0 : real -> Prop) := exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0)).
Definition term10 (x0 : real -> Prop) := exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term577 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((~ (@IN real x1 x0)) \/ (real_le x1 x2)).
Definition term204 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x1.
Definition term181 (x0 : real -> Prop) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0)).
Definition term415 (x0 : type1021) (x1 : real -> Prop) := (x1 = (@EMPTY real)) \/ (forall y0 : real, (fun y1 : real => (@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) y0).
Definition term242 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0) \/ (real_le (sup x0) x1).
Definition term692 (x0 : real) (x1 : type1021) (x2 : real) (x3 : real -> Prop) := imp (~ ((x3 = (@EMPTY real)) \/ ((~ (real_le (x1 x3 x0) x0)) \/ (@IN real (x1 x3 x2) x3)))).
Definition term661 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := imp (~ ((x2 = (@EMPTY real)) \/ ((~ (real_le (x0 x2 x1) x1)) \/ (real_le (sup x2) x3)))).
Definition term635 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := imp (~ ((x2 = (@EMPTY real)) \/ ((@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3)))).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term551 (x0 : type1021) (x1 : real) (x2 : real -> Prop) := or (@IN real (x0 x2 x1) x2).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term609 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := and (real_le (x0 x1 x2) x2).
Definition term107 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 (sup x0)))) x1.
Definition term632 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := ~ ((@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3)).
Definition term599 (x0 : real) (x1 : real -> Prop) := or (real_le x0 (sup x1)).
Definition term466 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => (x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1)))) y0) \/ (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term250 (x0 : real -> Prop) (x1 : real) (x2 : real) := or ((@IN real x1 x0) /\ (~ (real_le x1 x2))).
Definition term417 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) x2.
Definition term17 (x0 : real -> Prop) := ((((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term16 (x0 : real -> Prop) := (((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> ((@FINITE real x0) /\ (~ (x0 = (@EMPTY real)))) -> (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term265 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => ((@IN real y2 x0) /\ (~ (real_le y2 y1))) \/ (real_le (sup x0) y1)) x1 y0.
Definition term208 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) x1 y0.
Definition term248 (x0 : real -> Prop) (x1 : real) := @eq Prop ((exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1))) \/ (real_le (sup x0) x1)).
Definition term247 (x0 : real -> Prop) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 x1))) y0) \/ (real_le (sup x0) x1)).
Definition term737 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term732 (x0 : real -> Prop) (x1 : real -> Prop) := ~ (~ (x0 = x1)).
Definition term402 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((@IN real (x0 x1 x2) x1) /\ (~ (real_le (x0 x1 x2) x2))) \/ (real_le (sup x1) x2).
Definition term271 (x0 : real -> real) (x1 : real -> Prop) (x2 : real) := ((@IN real (x0 x2) x1) /\ (~ (real_le (x0 x2) x2))) \/ (real_le (sup x1) x2).
Definition term252 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((@IN real x0 x1) /\ (~ (real_le x0 x2))) \/ (real_le (sup x1) x2).
Definition term237 (x0 : real -> Prop) := or (exists y0 : real -> real, (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))).
Definition term476 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ ((fun y0 : real => ((~ (@IN real y0 x2)) \/ (real_le y0 (sup x2))) /\ (((@IN real (x1 x2 y0) x2) /\ (~ (real_le (x1 x2 y0) y0))) \/ (real_le (sup x2) y0))) x3).
Definition term587 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (real_le (x0 x3 x1) x1)) \/ (real_le x2 (sup x3)).
Definition term150 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((@IN real x0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x0))) /\ ((fun y1 : real => (~ (@IN real (sup x1) x1)) \/ ((@IN real y1 x1) /\ (~ (real_le y1 (sup x1))))) y0).
Definition term163 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1)).
Definition term439 (x0 : real -> Prop) (x1 : real) := and ((fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 (sup x0))) x1).
Definition term365 (x0 : real) (x1 : real) := and ((fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1).
Definition term130 (x0 : real -> Prop) (x1 : real) := and ((fun y0 : real => (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0))) x1).
Definition term721 (x0 : real -> Prop) (x1 : real -> Prop) := or (~ (x0 = x1)).
Definition term630 (x0 : type1021) (x1 : real) (x2 : real -> Prop) (x3 : real) := ~ ((x2 = (@EMPTY real)) \/ ((@IN real (x0 x2 x1) x2) \/ (real_le (sup x2) x3))).
Definition term260 (x0 : real -> Prop) := fun y0 : real => fun y1 : real => ((@IN real y1 x0) /\ (~ (real_le y1 y0))) \/ (real_le (sup x0) y0).
Definition term533 (x0 : real) (x1 : real -> Prop) := ~ (real_le x0 (sup x1)).
Definition term198 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term156 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((@IN real x1 x0) -> real_le x1 x2).
Definition term151 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((@IN real x0 x1) /\ (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y1 x0))) /\ ((~ (@IN real (sup x1) x1)) \/ ((@IN real y0 x1) /\ (~ (real_le y0 (sup x1))))).
Definition term589 (x0 : real) (x1 : real -> Prop) := or (~ (@IN real x0 x1)).
Definition term602 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (x3 = (@EMPTY real)) \/ ((~ (real_le (x0 x3 x1) x1)) \/ (~ (@IN real x2 x3))).
Definition term184 (x0 : real -> Prop) (x1 : real) := or (exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1))).
Definition term404 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0))) \/ (real_le (sup x1) y0).
Definition term275 (x0 : real -> real) (x1 : real -> Prop) := forall y0 : real, ((@IN real (x0 y0) x1) /\ (~ (real_le (x0 y0) y0))) \/ (real_le (sup x1) y0).
Definition term467 (x0 : type1021) (x1 : real -> Prop) := fun y0 : real => ((x1 = (@EMPTY real)) \/ ((@IN real (x0 x1 y0) x1) /\ (~ (real_le (x0 x1 y0) y0)))) \/ (forall y1 : real, ((~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) /\ (((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1))).
Definition term539 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> Prop) := (~ (x2 = x0)) \/ ((@IN real x0 x1) \/ (~ (@IN real x2 x3))).
Definition term296 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term26 := (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term29 (x0 : real -> Prop) := (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term97 (x0 : real -> Prop) := and (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 y0))).
Definition term96 (x0 : real -> Prop) := and (exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term30 (x0 : real -> Prop) := (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))) -> (forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term708 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) /\ (~ (~ (real_le x0 x1))).
Definition term715 (x0 : real -> Prop) (x1 : real) := (real_le x1 (sup x0)) /\ (real_le (sup x0) x1).
Definition term751 (x0 : real) (x1 : real -> Prop) := (real_le x0 (sup x1)) -> False.
Definition term318 := forall y0 : real -> Prop, exists y1 : real -> real, ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2))).
Definition term752 (x0 : real -> Prop) := (fun y0 : real -> Prop => ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> (~ ((exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (@IN real (sup y0) y0) /\ (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)))) -> (forall y1 : real -> Prop, ((~ (y1 = (@EMPTY real))) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y1) -> real_le y3 y2)) -> (forall y2 : real, (@IN real y2 y1) -> real_le y2 (sup y1)) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y1) -> real_le y3 y2) -> real_le (sup y1) y2)) -> (forall y1 : real, forall y2 : real, (real_le y1 y2) \/ (real_le y2 y1)) -> (forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) = (y1 = y2)) -> False) x0.
Definition term545 (x0 : real -> Prop) := (x0 = (@EMPTY real)) -> ~ (x0 = (@EMPTY real)).
Definition term373 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0)).
Definition term429 (x0 : type1021) (x1 : real -> Prop) := forall y0 : real, ((fun y1 : real => (~ (@IN real y1 x1)) \/ (real_le y1 (sup x1))) y0) /\ ((fun y1 : real => ((@IN real (x0 x1 y1) x1) /\ (~ (real_le (x0 x1 y1) y1))) \/ (real_le (sup x1) y1)) y0).
Definition term382 := forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term359 (x0 : real) := forall y0 : real, ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term185 (x0 : real -> Prop) (x1 : real) := (~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1)) \/ (real_le (sup x0) x1).
Definition term115 (x0 : real -> Prop) := fun y0 : real => (~ (@IN real (sup x0) x0)) \/ ((@IN real y0 x0) /\ (~ (real_le y0 (sup x0)))).
Definition term469 (x0 : real) (x1 : type1021) (x2 : real -> Prop) := ((x2 = (@EMPTY real)) \/ ((@IN real (x1 x2 x0) x2) /\ (~ (real_le (x1 x2 x0) x0)))) \/ (forall y0 : real, (fun y1 : real => ((~ (@IN real y1 x2)) \/ (real_le y1 (sup x2))) /\ (((@IN real (x1 x2 y1) x2) /\ (~ (real_le (x1 x2 y1) y1))) \/ (real_le (sup x2) y1))) y0).
Definition term64 (x0 : real -> Prop) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0).
Definition term28 (x0 : real -> Prop) := imp (~ ((exists y0 : real, (@IN real y0 x0) /\ (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (@IN real (sup x0) x0) /\ (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)))).
Definition term608 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := and (~ (~ (real_le (x0 x1 x2) x2))).
Definition term7 (x0 : real -> Prop) := (fun y0 : real -> Prop => ((@FINITE real y0) /\ (~ (y0 = (@EMPTY real)))) -> exists y1 : real, (@IN real y1 y0) /\ (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) x0.
Definition term324 (x0 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real -> real => ((y0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2)))) \/ ((forall y2 : real, (~ (@IN real y2 y0)) \/ (real_le y2 (sup y0))) /\ (forall y2 : real, ((@IN real (y1 y2) y0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup y0) y2)))) x0.
Definition term510 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2)))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (@IN real x3 x2)) \/ (real_le x3 (sup x2))))) /\ (((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)))) /\ ((((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))) /\ (((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0))) \/ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))))).
Definition term116 (x0 : real -> Prop) := exists y0 : real, (~ (@IN real (sup x0) x0)) \/ ((@IN real y0 x0) /\ (~ (real_le y0 (sup x0)))).
Definition term493 (x0 : real) (x1 : type1021) (x2 : real -> Prop) (x3 : real) := (((x2 = (@EMPTY real)) \/ (@IN real (x1 x2 x0) x2)) /\ ((x2 = (@EMPTY real)) \/ (~ (real_le (x1 x2 x0) x0)))) \/ (((@IN real (x1 x2 x3) x2) \/ (real_le (sup x2) x3)) /\ ((~ (real_le (x1 x2 x3) x3)) \/ (real_le (sup x2) x3))).
Definition term546 (x0 : Prop) := x0 -> ~ x0.
Definition term384 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1)).
Definition term112 (x0 : real -> Prop) (x1 : real) := (~ (@IN real (sup x0) x0)) \/ ((fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 (sup x0)))) x1).
Definition term364 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1)).
Definition term378 (x0 : real) := forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0).
Definition term233 (x0 : real -> Prop) (x1 : real -> real) := (x0 = (@EMPTY real)) \/ (forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0))).
Definition term666 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((~ (x1 = (@EMPTY real))) /\ ((real_le (x0 x1 x2) x2) /\ (~ (real_le (sup x1) x2)))) -> ~ (real_le (x0 x1 x2) x2).
Definition term62 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term580 (x0 : real) (x1 : real -> Prop) := imp (~ (~ (@IN real x0 x1))).
Definition term485 (x0 : type1021) (x1 : real -> Prop) (x2 : real) := ((@IN real (x0 x1 x2) x1) \/ (real_le (sup x1) x2)) /\ ((~ (real_le (x0 x1 x2) x2)) \/ (real_le (sup x1) x2)).
Definition term611 (x0 : type1021) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (x3 = (@EMPTY real))) /\ ((real_le (x0 x3 x1) x1) /\ (@IN real x2 x3)).
Definition term309 (x0 : real -> Prop) := @eq Prop ((exists y0 : real -> real, (x0 = (@EMPTY real)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))) \/ (exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y1 (sup x0))) /\ (forall y1 : real, ((@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) \/ (real_le (sup x0) y1)))).
Definition term308 (x0 : real -> Prop) := @eq Prop ((exists y0 : real -> real, (fun y1 : real -> real => (x0 = (@EMPTY real)) \/ (forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2)))) y0) \/ (exists y0 : real -> real, (fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y2 (sup x0))) /\ (forall y2 : real, ((@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) \/ (real_le (sup x0) y2))) y0)).
