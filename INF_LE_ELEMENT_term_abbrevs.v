Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term390 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ ((@IN real (x0 x3 x1 x4 x2) x3) \/ (real_le (inf x3) x4))).
Definition term68 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ((exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) /\ (@IN real y0 x0)) -> real_le (inf x0) y0) x1.
Definition term470 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := imp (~ ((~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4)))))).
Definition term409 (x0 : real -> Prop) (x1 : real) (x2 : real) := (real_le (inf x0) x2) \/ ((~ (@IN real x1 x0)) \/ (~ (real_le x1 x2))).
Definition term367 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ (@IN real (x0 x3 x1 x4 x2) x3))) /\ ((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ (~ (real_le x1 (x0 x3 x1 x4 x2)))))) \/ (real_le (inf x3) x4).
Definition term47 (x0 : real -> Prop) (x1 : real) := ((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ (@IN real x1 x0)) -> real_le (inf x0) x1.
Definition term73 (x0 : type1022) := ~ (all x0).
Definition term64 (x0 : real -> Prop) := ~ (all x0).
Definition term478 := (~ False) -> False.
Definition term288 (x0 : real) (x1 : real -> Prop) (x2 : type1627) := (fun y0 : type1627 => forall y1 : real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (y0 y1 y2) x1) /\ (~ (real_le x0 (y0 y1 y2)))))) \/ (real_le (inf x1) y1)) x2.
Definition term451 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (~ (real_le x1 (x0 x2 x1 x4 x3))) \/ ((real_le (inf x2) x4) \/ (~ (real_le x3 x4))).
Definition term152 (x0 : real -> Prop) (x1 : Prop) := forall y0 : real, (x0 y0) \/ x1.
Definition term203 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := fun y0 : real => (~ (@IN real x0 x2)) \/ ((fun y1 : real => (~ (real_le x0 x1)) \/ ((@IN real y1 x2) /\ (~ (real_le x3 y1)))) y0).
Definition term189 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := fun y0 : real => (~ (real_le x0 x1)) \/ ((fun y1 : real => (@IN real y1 x2) /\ (~ (real_le x3 y1))) y0).
Definition term201 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (~ (@IN real x0 x2)) \/ ((fun y0 : real => (~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0)))) x4).
Definition term80 := exists y0 : real -> Prop, exists y1 : real, ((exists y2 : real, forall y3 : real, (~ (@IN real y3 y0)) \/ (real_le y2 y3)) /\ (@IN real y1 y0)) /\ (~ (real_le (inf y0) y1)).
Definition term137 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := ~ ((@IN real x0 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x3 y0))).
Definition term183 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le x1 y1))) y0.
Definition term387 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (~ (@IN real x2 x3)) \/ (((~ (real_le x2 x4)) \/ (@IN real (x0 x3 x1 x4 x2) x3)) \/ (real_le (inf x3) x4)).
Definition term421 (x0 : Prop) := ~ (~ x0).
Definition term135 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (@IN real x0 x2)) \/ (~ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x3 y0))).
Definition term416 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real) (x4 : real -> Prop) := (~ ((~ (@IN real x3 x4)) \/ ((~ (real_le x3 x2)) \/ (real_le (inf x4) x2)))) -> @IN real (x0 x4 x1 x2 x3) x4.
Definition term420 (x0 : real) (x1 : real -> Prop) (x2 : real) := (~ (~ (@IN real x0 x1))) /\ (~ ((~ (real_le x0 x2)) \/ (real_le (inf x1) x2))).
Definition term192 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (@IN real x0 x2)) \/ (exists y0 : real, (~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0)))).
Definition term75 := exists y0 : real -> Prop, ~ ((fun y1 : real -> Prop => forall y2 : real, ((exists y3 : real, forall y4 : real, (@IN real y4 y1) -> real_le y3 y4) /\ (@IN real y2 y1)) -> real_le (inf y1) y2) y0).
Definition term139 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := or ((~ (@IN real x0 x2)) \/ ((~ (real_le x0 x1)) \/ (exists y0 : real, (@IN real y0 x2) /\ (~ (real_le x3 y0))))).
Definition term128 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) /\ (~ (real_le x1 y0)).
Definition term425 (x0 : real) (x1 : real -> Prop) (x2 : real) := (~ (~ (real_le x0 x2))) /\ (~ (real_le (inf x1) x2)).
Definition term94 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le x1 y0)).
Definition term426 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term111 (x0 : real) (x1 : real) (x2 : real -> Prop) := and ((forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)) /\ (@IN real x1 x2)).
Definition term468 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (real_le x4 x3) /\ (real_le x2 (x0 x1 x2 x3 x4)).
Definition term115 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)) /\ (@IN real x1 x0)) /\ (~ (real_le (inf x0) x1)).
Definition term327 := fun y0 : type1018 => forall y1 : real -> Prop, forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y1)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y0 y1 y2 y3 y4) y1) /\ (~ (real_le y2 (y0 y1 y2 y3 y4)))))) \/ (real_le (inf y1) y3).
Definition term263 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := (fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x0 (y0 y1)))))) \/ (real_le (inf x1) x2)) x3.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term105 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)) /\ (@IN real x0 x1)) y0.
Definition term291 (x0 : real -> Prop) := fun y0 : real => exists y1 : type1627, (fun y2 : real => fun y3 : type1627 => forall y4 : real, (forall y5 : real, (~ (@IN real y5 x0)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y3 y4 y5) x0) /\ (~ (real_le y2 (y3 y4 y5)))))) \/ (real_le (inf x0) y4)) y0 y1.
Definition term266 (x0 : real) (x1 : real -> Prop) := fun y0 : real => exists y1 : real -> real, (fun y2 : real => fun y3 : real -> real => (forall y4 : real, (~ (@IN real y4 x1)) \/ ((~ (real_le y4 y2)) \/ ((@IN real (y3 y4) x1) /\ (~ (real_le x0 (y3 y4)))))) \/ (real_le (inf x1) y2)) y0 y1.
Definition term55 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1).
Definition term43 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1.
Definition term62 (x0 : real -> Prop) (x1 : real) := ((exists y0 : real, forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)) /\ (@IN real x1 x0)) /\ (~ (real_le (inf x0) x1)).
Definition term61 (x0 : real -> Prop) (x1 : real) := ((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ (@IN real x1 x0)) /\ (~ (real_le (inf x0) x1)).
Definition term99 (x0 : real) (x1 : real -> Prop) := exists y0 : real, (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x0 x1).
Definition term261 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) \/ (real_le (inf x1) y0)) x2.
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term235 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term123 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le x1 y0).
Definition term66 (x0 : real -> Prop) := ~ (forall y0 : real, ((exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) /\ (@IN real y0 x0)) -> real_le (inf x0) y0).
Definition term216 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (fun y0 : real => fun y1 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real y1 x1) /\ (~ (real_le x2 y1))))) x3 x4.
Definition term51 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x2 x0)) \/ (real_le x1 x2).
Definition term60 (x0 : real) (x1 : real -> Prop) := and ((exists y0 : real, forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x0 x1)).
Definition term59 (x0 : real) (x1 : real -> Prop) := and ((exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) /\ (@IN real x0 x1)).
Definition term460 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (real_le (inf x1) x3) \/ ((~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4))))).
Definition term214 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => fun y1 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real y1 x1) /\ (~ (real_le x2 y1)))).
Definition term347 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := ((fun y0 : real => (~ (@IN real y0 x3)) \/ ((~ (real_le y0 x4)) \/ ((@IN real (x0 x3 x1 x4 y0) x3) /\ (~ (real_le x1 (x0 x3 x1 x4 y0)))))) x2) \/ (real_le (inf x3) x4).
Definition term84 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term413 (x0 : real) (x1 : real -> Prop) (x2 : real) := (~ (@IN real x0 x1)) \/ ((~ (real_le x0 x2)) \/ (real_le (inf x1) x2)).
Definition term290 (x0 : real -> Prop) (x1 : real) := exists y0 : type1627, (fun y1 : real => fun y2 : type1627 => forall y3 : real, (forall y4 : real, (~ (@IN real y4 x0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y2 y3 y4) x0) /\ (~ (real_le y1 (y2 y3 y4)))))) \/ (real_le (inf x0) y3)) x1 y0.
Definition term419 (x0 : real) (x1 : real -> Prop) (x2 : real) := ~ ((~ (@IN real x0 x1)) \/ ((~ (real_le x0 x2)) \/ (real_le (inf x1) x2))).
Definition term194 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := exists y0 : real, (~ (@IN real x0 x2)) \/ ((fun y1 : real => (~ (real_le x0 x1)) \/ ((@IN real y1 x2) /\ (~ (real_le x3 y1)))) y0).
Definition term180 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := exists y0 : real, (~ (real_le x0 x1)) \/ ((fun y1 : real => (@IN real y1 x2) /\ (~ (real_le x3 y1))) y0).
Definition term154 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, ((fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x0 y2))))) y0) \/ (real_le (inf x1) x2).
Definition term445 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := (@IN real (x0 x1 x2 x3 x3) x1) -> real_le x2 (x0 x1 x2 x3 x3).
Definition term226 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real y2 x1) /\ (~ (real_le x2 y2))))) y0 (x3 y0).
Definition term69 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => ((exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) /\ (@IN real y0 x0)) -> real_le (inf x0) y0) x1).
Definition term242 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x2 (y1 y2)))))) y0.
Definition term218 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real y2 x1) /\ (~ (real_le x2 y2))))) x3 y0.
Definition term274 (x0 : real) (x1 : real -> Prop) (x2 : type1627) := forall y0 : real, (fun y1 : real => fun y2 : real -> real => (forall y3 : real, (~ (@IN real y3 x1)) \/ ((~ (real_le y3 y1)) \/ ((@IN real (y2 y3) x1) /\ (~ (real_le x0 (y2 y3)))))) \/ (real_le (inf x1) y1)) y0 (x2 y0).
Definition term253 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real -> real, (forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x0 (y0 y1)))))) \/ (real_le (inf x1) x2).
Definition term415 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term350 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := fun y0 : real => ((~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x2 x1 x3 y0) x2) /\ (~ (real_le x1 (x0 x2 x1 x3 y0)))))) \/ (real_le (inf x2) x3).
Definition term475 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := ((@IN real x3 x2) /\ ((real_le x3 x3) /\ (real_le x1 (x0 x2 x1 x3 x3)))) -> real_le (inf x2) x3.
Definition term220 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x0)) \/ ((@IN real y3 x1) /\ (~ (real_le x2 y3))))) y0 y1.
Definition term359 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := ((~ (real_le x4 x3)) \/ (@IN real (x0 x1 x2 x3 x4) x1)) /\ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4)))).
Definition term378 (x0 : type1018) := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, (((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (@IN real (x0 y0 y1 y2 y3) y0))) \/ (real_le (inf y0) y2)) /\ (((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (~ (real_le y1 (x0 y0 y1 y2 y3))))) \/ (real_le (inf y0) y2)).
Definition term357 (x0 : type1018) := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (x0 y0 y1 y2 y3) y0) /\ (~ (real_le y1 (x0 y0 y1 y2 y3)))))) \/ (real_le (inf y0) y2).
Definition term325 (x0 : type1018) := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, (forall y3 : real, (~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (x0 y0 y1 y2 y3) y0) /\ (~ (real_le y1 (x0 y0 y1 y2 y3)))))) \/ (real_le (inf y0) y2).
Definition term174 := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, (forall y3 : real, (~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (exists y4 : real, (@IN real y4 y0) /\ (~ (real_le y1 y4))))) \/ (real_le (inf y0) y2).
Definition term149 := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (exists y4 : real, (@IN real y4 y0) /\ (~ (real_le y1 y4))))) \/ (real_le (inf y0) y2).
Definition term17 := forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2.
Definition term386 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := ((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ (@IN real (x0 x3 x1 x4 x2) x3))) \/ (real_le (inf x3) x4).
Definition term237 (x0 : type1028) (x1 : Prop) := (exists y0 : real -> real, x0 y0) \/ x1.
Definition term120 := exists y0 : real -> Prop, exists y1 : real, exists y2 : real, ((forall y3 : real, (~ (@IN real y3 y0)) \/ (real_le y2 y3)) /\ (@IN real y1 y0)) /\ (~ (real_le (inf y0) y1)).
Definition term286 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : type1627 => forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y1 y2 y3) x0) /\ (~ (real_le y0 (y1 y2 y3)))))) \/ (real_le (inf x0) y2)) x1.
Definition term392 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := ((~ (real_le x2 x4)) \/ (~ (real_le x1 (x0 x3 x1 x4 x2)))) \/ (real_le (inf x3) x4).
Definition term476 (x0 : real -> Prop) (x1 : real) := (~ (real_le (inf x0) x1)) -> real_le (inf x0) x1.
Definition term432 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real) (x4 : real -> Prop) := ((@IN real x3 x4) /\ ((real_le x3 x2) /\ (~ (real_le (inf x4) x2)))) -> @IN real (x0 x4 x1 x2 x3) x4.
Definition term377 (x0 : type1018) := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, forall y3 : real, (((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (@IN real (x0 y0 y1 y2 y3) y0))) \/ (real_le (inf y0) y2)) /\ (((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (~ (real_le y1 (x0 y0 y1 y2 y3))))) \/ (real_le (inf y0) y2)).
Definition term356 (x0 : type1018) := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, forall y3 : real, ((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (x0 y0 y1 y2 y3) y0) /\ (~ (real_le y1 (x0 y0 y1 y2 y3)))))) \/ (real_le (inf y0) y2).
Definition term323 (x0 : type1018) := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, (forall y3 : real, (~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (x0 y0 y1 y2 y3) y0) /\ (~ (real_le y1 (x0 y0 y1 y2 y3)))))) \/ (real_le (inf y0) y2).
Definition term302 (x0 : real -> Prop) := fun y0 : type1625 => forall y1 : real, forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y0 y1 y2 y3) x0) /\ (~ (real_le y1 (y0 y1 y2 y3)))))) \/ (real_le (inf x0) y2).
Definition term173 := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, (forall y3 : real, (~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (exists y4 : real, (@IN real y4 y0) /\ (~ (real_le y1 y4))))) \/ (real_le (inf y0) y2).
Definition term148 := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, forall y3 : real, ((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (exists y4 : real, (@IN real y4 y0) /\ (~ (real_le y1 y4))))) \/ (real_le (inf y0) y2).
Definition term39 := fun y0 : real -> Prop => forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2.
Definition term119 := fun y0 : real -> Prop => exists y1 : real, exists y2 : real, ((forall y3 : real, (~ (@IN real y3 y0)) \/ (real_le y2 y3)) /\ (@IN real y1 y0)) /\ (~ (real_le (inf y0) y1)).
Definition term16 := ~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2).
Definition term10 := ~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1).
Definition term396 (x0 : Prop) := (~ x0) -> x0.
Definition term125 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le x1 y0) x2.
Definition term441 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((real_le x0 x1) \/ (~ (@IN real x1 x2))).
Definition term12 := ((~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False.
Definition term88 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) y0.
Definition term141 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := ((~ (@IN real x0 x2)) \/ ((~ (real_le x0 x3)) \/ (exists y0 : real, (@IN real y0 x2) /\ (~ (real_le x1 y0))))) \/ (real_le (inf x2) x3).
Definition term381 (x0 : type1018) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (((~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ (@IN real (x0 x1 y0 y1 y2) x1))) \/ (real_le (inf x1) y1)) /\ (((~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ (~ (real_le y0 (x0 x1 y0 y1 y2))))) \/ (real_le (inf x1) y1))) x2.
Definition term28 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x3 y0).
Definition term418 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term200 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := @eq Prop ((~ (@IN real x0 x2)) \/ (exists y0 : real, (~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0))))).
Definition term199 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := @eq Prop ((~ (@IN real x0 x2)) \/ (exists y0 : real, (fun y1 : real => (~ (real_le x0 x1)) \/ ((@IN real y1 x2) /\ (~ (real_le x3 y1)))) y0)).
Definition term186 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := @eq Prop ((~ (real_le x0 x1)) \/ (exists y0 : real, (@IN real y0 x2) /\ (~ (real_le x3 y0)))).
Definition term185 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := @eq Prop ((~ (real_le x0 x1)) \/ (exists y0 : real, (fun y1 : real => (@IN real y1 x2) /\ (~ (real_le x3 y1))) y0)).
Definition term208 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term449 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (~ (real_le x1 (x0 x3 x1 x4 x2))) \/ ((~ (real_le x2 x4)) \/ (real_le (inf x3) x4)).
Definition term159 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := ((fun y0 : real => (~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ (exists y1 : real, (@IN real y1 x2) /\ (~ (real_le x0 y1))))) x1) \/ (real_le (inf x2) x3).
Definition term326 := fun y0 : type1018 => forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : type1625 => forall y4 : real, forall y5 : real, (forall y6 : real, (~ (@IN real y6 y2)) \/ ((~ (real_le y6 y5)) \/ ((@IN real (y3 y4 y5 y6) y2) /\ (~ (real_le y4 (y3 y4 y5 y6)))))) \/ (real_le (inf y2) y5)) y1 (y0 y1).
Definition term198 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := exists y0 : real, (fun y1 : real => (~ (real_le x0 x1)) \/ ((@IN real y1 x2) /\ (~ (real_le x3 y1)))) y0.
Definition term184 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => (@IN real y1 x0) /\ (~ (real_le x1 y1))) y0.
Definition term106 (x0 : real) (x1 : real -> Prop) := exists y0 : real, (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)) /\ (@IN real x0 x1)) y0.
Definition term428 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_le x0 x2) /\ (~ (real_le (inf x1) x2)).
Definition term233 (x0 : real) (x1 : real -> Prop) (x2 : real) := or (exists y0 : real -> real, forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x2 (y0 y1)))))).
Definition term376 (x0 : type1018) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, forall y2 : real, (((~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ (@IN real (x0 x1 y0 y1 y2) x1))) \/ (real_le (inf x1) y1)) /\ (((~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ (~ (real_le y0 (x0 x1 y0 y1 y2))))) \/ (real_le (inf x1) y1)).
Definition term374 (x0 : type1018) (x1 : real) (x2 : real -> Prop) := forall y0 : real, forall y1 : real, (((~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ (@IN real (x0 x2 x1 y0 y1) x2))) \/ (real_le (inf x2) y0)) /\ (((~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ (~ (real_le x1 (x0 x2 x1 y0 y1))))) \/ (real_le (inf x2) y0)).
Definition term355 (x0 : type1018) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (x0 x1 y0 y1 y2) x1) /\ (~ (real_le y0 (x0 x1 y0 y1 y2)))))) \/ (real_le (inf x1) y1).
Definition term353 (x0 : type1018) (x1 : real) (x2 : real -> Prop) := forall y0 : real, forall y1 : real, ((~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ ((@IN real (x0 x2 x1 y0 y1) x2) /\ (~ (real_le x1 (x0 x2 x1 y0 y1)))))) \/ (real_le (inf x2) y0).
Definition term321 (x0 : type1018) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (x0 x1 y0 y1 y2) x1) /\ (~ (real_le y0 (x0 x1 y0 y1 y2)))))) \/ (real_le (inf x1) y1).
Definition term300 (x0 : type1625) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (x0 y0 y1 y2) x1) /\ (~ (real_le y0 (x0 y0 y1 y2)))))) \/ (real_le (inf x1) y1).
Definition term172 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ ((~ (real_le y2 y1)) \/ (exists y3 : real, (@IN real y3 x0) /\ (~ (real_le y0 y3))))) \/ (real_le (inf x0) y1).
Definition term147 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (@IN real y2 x0)) \/ ((~ (real_le y2 y1)) \/ (exists y3 : real, (@IN real y3 x0) /\ (~ (real_le y0 y3))))) \/ (real_le (inf x0) y1).
Definition term145 (x0 : real) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, ((~ (@IN real y1 x1)) \/ ((~ (real_le y1 y0)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x0 y2))))) \/ (real_le (inf x1) y0).
Definition term38 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, forall y2 : real, ((@IN real y2 x0) /\ ((real_le y2 y1) /\ (forall y3 : real, (@IN real y3 x0) -> real_le y0 y3))) -> real_le (inf x0) y1.
Definition term36 (x0 : real) (x1 : real -> Prop) := forall y0 : real, forall y1 : real, ((@IN real y1 x1) /\ ((real_le y1 y0) /\ (forall y2 : real, (@IN real y2 x1) -> real_le x0 y2))) -> real_le (inf x1) y0.
Definition term41 := forall y0 : real, real_le y0 y0.
Definition term246 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop ((exists y0 : real -> real, forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x0 (y0 y1)))))) \/ (real_le (inf x1) x2)).
Definition term245 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop ((exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x2)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) y0) \/ (real_le (inf x1) x2)).
Definition term122 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) /\ (~ (real_le x1 x2)).
Definition term309 := exists y0 : type1018, forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : type1625 => forall y4 : real, forall y5 : real, (forall y6 : real, (~ (@IN real y6 y2)) \/ ((~ (real_le y6 y5)) \/ ((@IN real (y3 y4 y5 y6) y2) /\ (~ (real_le y4 (y3 y4 y5 y6)))))) \/ (real_le (inf y2) y5)) y1 (y0 y1).
Definition term307 (x0 : type1015) := exists y0 : type1018, forall y1 : real -> Prop, x0 y1 (y0 y1).
Definition term284 (x0 : real -> Prop) := exists y0 : type1625, forall y1 : real, (fun y2 : real => fun y3 : type1627 => forall y4 : real, (forall y5 : real, (~ (@IN real y5 x0)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y3 y4 y5) x0) /\ (~ (real_le y2 (y3 y4 y5)))))) \/ (real_le (inf x0) y4)) y1 (y0 y1).
Definition term282 (x0 : type1617) := exists y0 : type1625, forall y1 : real, x0 y1 (y0 y1).
Definition term278 (x0 : real) (x1 : real -> Prop) := exists y0 : type1627, forall y1 : real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (y0 y1 y2) x1) /\ (~ (real_le x0 (y0 y1 y2)))))) \/ (real_le (inf x1) y1).
Definition term259 (x0 : real) (x1 : real -> Prop) := exists y0 : type1627, forall y1 : real, (fun y2 : real => fun y3 : real -> real => (forall y4 : real, (~ (@IN real y4 x1)) \/ ((~ (real_le y4 y2)) \/ ((@IN real (y3 y4) x1) /\ (~ (real_le x0 (y3 y4)))))) \/ (real_le (inf x1) y2)) y1 (y0 y1).
Definition term257 (x0 : type1618) := exists y0 : type1627, forall y1 : real, x0 y1 (y0 y1).
Definition term232 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real -> real, forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x2 (y0 y1))))).
Definition term213 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x0)) \/ ((@IN real y3 x1) /\ (~ (real_le x2 y3))))) y1 (y0 y1).
Definition term211 (x0 : type1626) := exists y0 : real -> real, forall y1 : real, x0 y1 (y0 y1).
Definition term372 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := forall y0 : real, (((~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ (@IN real (x0 x2 x1 x3 y0) x2))) \/ (real_le (inf x2) x3)) /\ (((~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ (~ (real_le x1 (x0 x2 x1 x3 y0))))) \/ (real_le (inf x2) x3)).
Definition term118 (x0 : real -> Prop) := exists y0 : real, exists y1 : real, ((forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) /\ (@IN real y0 x0)) /\ (~ (real_le (inf x0) y0)).
Definition term461 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (~ ((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ (~ (real_le x1 (x0 x3 x1 x4 x2)))))) -> real_le (inf x3) x4.
Definition term361 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := ~ (real_le x2 (x0 x1 x2 x3 x4)).
Definition term332 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := or (forall y0 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x1 x2 x3 y0) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 y0)))))).
Definition term248 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := or (forall y0 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real (x3 y0) x1) /\ (~ (real_le x2 (x3 y0)))))).
Definition term167 (x0 : real) (x1 : real -> Prop) (x2 : real) := or (forall y0 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x2 y1))))).
Definition term467 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := real_le x2 (x0 x1 x2 x3 x4).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term471 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := imp ((@IN real x4 x1) /\ ((real_le x4 x3) /\ (real_le x2 (x0 x1 x2 x3 x4)))).
Definition term297 (x0 : real -> Prop) (x1 : type1625) := fun y0 : real => (fun y1 : real => fun y2 : type1627 => forall y3 : real, (forall y4 : real, (~ (@IN real y4 x0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y2 y3 y4) x0) /\ (~ (real_le y1 (y2 y3 y4)))))) \/ (real_le (inf x0) y3)) y0 (x1 y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term305 := forall y0 : real -> Prop, exists y1 : type1625, forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y1 y2 y3 y4) y0) /\ (~ (real_le y2 (y1 y2 y3 y4)))))) \/ (real_le (inf y0) y3).
Definition term22 := (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> ~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2).
Definition term265 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real -> real, (fun y1 : real => fun y2 : real -> real => (forall y3 : real, (~ (@IN real y3 x1)) \/ ((~ (real_le y3 y1)) \/ ((@IN real (y2 y3) x1) /\ (~ (real_le x0 (y2 y3)))))) \/ (real_le (inf x1) y1)) x2 y0.
Definition term92 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x0 x1)).
Definition term91 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)) y0) /\ (@IN real x0 x1)).
Definition term63 (x0 : real -> Prop) (x1 : real) := ~ (((exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ (@IN real x1 x0)) -> real_le (inf x0) x1).
Definition term34 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, ((@IN real y0 x1) /\ ((real_le y0 x2) /\ (forall y1 : real, (@IN real y1 x1) -> real_le x0 y1))) -> real_le (inf x1) x2.
Definition term429 (x0 : real) (x1 : real -> Prop) (x2 : real) := (@IN real x0 x1) /\ ((real_le x0 x2) /\ (~ (real_le (inf x1) x2))).
Definition term71 (x0 : real -> Prop) := fun y0 : real => ((exists y1 : real, forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) /\ (@IN real y0 x0)) /\ (~ (real_le (inf x0) y0)).
Definition term398 (x0 : real) := ~ (real_le x0 x0).
Definition term407 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (@IN real (x0 x2 x1 x4 x3) x2) \/ ((~ (@IN real x3 x2)) \/ ((real_le (inf x2) x4) \/ (~ (real_le x3 x4)))).
Definition term124 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) -> real_le x1 y1) y0).
Definition term67 (x0 : real -> Prop) := exists y0 : real, ~ ((fun y1 : real => ((exists y2 : real, forall y3 : real, (@IN real y3 x0) -> real_le y2 y3) /\ (@IN real y1 x0)) -> real_le (inf x0) y1) y0).
Definition term340 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := fun y0 : real => (fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (x0 x1 x2 x3 y1) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 y1)))))) y0.
Definition term197 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := fun y0 : real => (fun y1 : real => (~ (real_le x0 x1)) \/ ((@IN real y1 x2) /\ (~ (real_le x3 y1)))) y0.
Definition term163 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => (fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x2 y2))))) y0.
Definition term109 (x0 : real -> Prop) (x1 : real) := @eq Prop ((exists y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)) /\ (@IN real x1 x0)) /\ (~ (real_le (inf x0) x1))).
Definition term108 (x0 : real -> Prop) (x1 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) /\ (@IN real x1 x0)) y0) /\ (~ (real_le (inf x0) x1))).
Definition term76 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1) x0.
Definition term465 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (~ (real_le x4 x3))) /\ (~ (~ (real_le x2 (x0 x1 x2 x3 x4)))).
Definition term339 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (fun y0 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x1 x2 x3 y0) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 y0)))))) x4.
Definition term217 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (fun y0 : real => (~ (@IN real x0 x2)) \/ ((~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0))))) x4.
Definition term331 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := forall y0 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x1 x2 x3 y0) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 y0))))).
Definition term229 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := forall y0 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real (x3 y0) x1) /\ (~ (real_le x2 (x3 y0))))).
Definition term294 (x0 : real -> Prop) (x1 : type1625) (x2 : real) := (fun y0 : real => fun y1 : type1627 => forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y1 y2 y3) x0) /\ (~ (real_le y0 (y1 y2 y3)))))) \/ (real_le (inf x0) y2)) x2 (x1 x2).
Definition term393 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (~ (real_le x2 x4)) \/ ((~ (real_le x1 (x0 x3 x1 x4 x2))) \/ (real_le (inf x3) x4)).
Definition term473 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := (real_le x3 x3) /\ (real_le x2 (x0 x1 x2 x3 x3)).
Definition term247 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := or ((fun y0 : real -> real => forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x2 (y0 y1)))))) x3).
Definition term270 (x0 : real) (x1 : real -> Prop) (x2 : type1627) (x3 : real) := (fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x0 (y0 y1)))))) \/ (real_le (inf x1) x3)) (x2 x3).
Definition term380 (x0 : type1018) (x1 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, forall y2 : real, forall y3 : real, (((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (@IN real (x0 y0 y1 y2 y3) y0))) \/ (real_le (inf y0) y2)) /\ (((~ (@IN real y3 y0)) \/ ((~ (real_le y3 y2)) \/ (~ (real_le y1 (x0 y0 y1 y2 y3))))) \/ (real_le (inf y0) y2))) x1.
Definition term313 (x0 : real -> Prop) (x1 : type1625) := (fun y0 : type1625 => forall y1 : real, forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y0 y1 y2 y3) x0) /\ (~ (real_le y1 (y0 y1 y2 y3)))))) \/ (real_le (inf x0) y2)) x1.
Definition term162 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop (forall y0 : real, ((~ (@IN real y0 x1)) \/ ((~ (real_le y0 x2)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x0 y1))))) \/ (real_le (inf x1) x2)).
Definition term161 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x0 y2))))) y0) \/ (real_le (inf x1) x2)).
Definition term430 (x0 : real) (x1 : real -> Prop) (x2 : real) := imp (~ ((~ (@IN real x0 x1)) \/ ((~ (real_le x0 x2)) \/ (real_le (inf x1) x2)))).
Definition term463 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (~ (@IN real x4 x1))) /\ (~ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4))))).
Definition term219 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real y2 x1) /\ (~ (real_le x2 y2))))) x3 y0.
Definition term188 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (~ (real_le x0 x1)) \/ ((@IN real x4 x2) /\ (~ (real_le x3 x4))).
Definition term117 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, ((forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) /\ (@IN real y0 x0)) /\ (~ (real_le (inf x0) y0)).
Definition term289 (x0 : real -> Prop) (x1 : real) := fun y0 : type1627 => (fun y1 : real => fun y2 : type1627 => forall y3 : real, (forall y4 : real, (~ (@IN real y4 x0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y2 y3 y4) x0) /\ (~ (real_le y1 (y2 y3 y4)))))) \/ (real_le (inf x0) y3)) x1 y0.
Definition term401 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (@IN real (x0 x3 x1 x4 x2) x3) \/ ((~ (real_le x2 x4)) \/ (real_le (inf x3) x4)).
Definition term439 (x0 : real) (x1 : real) (x2 : real -> Prop) := (real_le x0 x1) \/ (~ (@IN real x1 x2)).
Definition term373 (x0 : type1018) (x1 : real) (x2 : real -> Prop) := fun y0 : real => forall y1 : real, (((~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ (@IN real (x0 x2 x1 y0 y1) x2))) \/ (real_le (inf x2) y0)) /\ (((~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ (~ (real_le x1 (x0 x2 x1 y0 y1))))) \/ (real_le (inf x2) y0)).
Definition term295 (x0 : real -> Prop) (x1 : type1625) (x2 : real) := (fun y0 : type1627 => forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (y0 y1 y2) x0) /\ (~ (real_le x2 (y0 y1 y2)))))) \/ (real_le (inf x0) y1)) (x1 x2).
Definition term86 (x0 : real) (x1 : real -> Prop) := exists y0 : real, ((fun y1 : real => forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)) y0) /\ (@IN real x0 x1).
Definition term397 (x0 : real) := (~ (real_le x0 x0)) -> real_le x0 x0.
Definition term77 (x0 : real -> Prop) := ~ ((fun y0 : real -> Prop => forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1) x0).
Definition term15 := (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False.
Definition term399 (x0 : real -> Prop) (x1 : real) := (real_le (inf x0) x1) -> ~ (real_le (inf x0) x1).
Definition term412 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := @eq Prop ((@IN real (x0 x2 x1 x4 x3) x2) \/ ((real_le (inf x2) x4) \/ ((~ (@IN real x3 x2)) \/ (~ (real_le x3 x4))))).
Definition term453 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (@IN real x3 x1)) \/ ((real_le (inf x1) x4) \/ ((~ (real_le x2 (x0 x1 x2 x4 x3))) \/ (~ (real_le x3 x4)))).
Definition term96 (x0 : real) (x1 : real) (x2 : real -> Prop) := (forall y0 : real, (~ (@IN real y0 x2)) \/ (real_le x0 y0)) /\ (@IN real x1 x2).
Definition term442 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (~ (@IN real x2 x0))) -> real_le x1 x2.
Definition term243 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x2 (y1 y2)))))) y0.
Definition term308 := forall y0 : real -> Prop, exists y1 : type1625, (fun y2 : real -> Prop => fun y3 : type1625 => forall y4 : real, forall y5 : real, (forall y6 : real, (~ (@IN real y6 y2)) \/ ((~ (real_le y6 y5)) \/ ((@IN real (y3 y4 y5 y6) y2) /\ (~ (real_le y4 (y3 y4 y5 y6)))))) \/ (real_le (inf y2) y5)) y0 y1.
Definition term306 (x0 : type1015) := forall y0 : real -> Prop, exists y1 : type1625, x0 y0 y1.
Definition term450 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := or (~ (real_le x2 (x0 x1 x2 x3 x4))).
Definition term187 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (~ (real_le x0 x1)) \/ ((fun y0 : real => (@IN real y0 x2) /\ (~ (real_le x3 y0))) x4).
Definition term195 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term318 := @eq Prop (forall y0 : real -> Prop, exists y1 : type1625, forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y1 y2 y3 y4) y0) /\ (~ (real_le y2 (y1 y2 y3 y4)))))) \/ (real_le (inf y0) y3)).
Definition term317 := @eq Prop (forall y0 : real -> Prop, exists y1 : type1625, (fun y2 : real -> Prop => fun y3 : type1625 => forall y4 : real, forall y5 : real, (forall y6 : real, (~ (@IN real y6 y2)) \/ ((~ (real_le y6 y5)) \/ ((@IN real (y3 y4 y5 y6) y2) /\ (~ (real_le y4 (y3 y4 y5 y6)))))) \/ (real_le (inf y2) y5)) y0 y1).
Definition term389 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (~ (real_le x2 x4)) \/ ((@IN real (x0 x3 x1 x4 x2) x3) \/ (real_le (inf x3) x4)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term458 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (@IN real x3 x1)) \/ ((~ (real_le x2 (x0 x1 x2 x4 x3))) \/ (~ (real_le x3 x4))).
Definition term228 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real y2 x1) /\ (~ (real_le x2 y2))))) y0 (x3 y0).
Definition term293 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : type1627, forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y1 y2 y3) x0) /\ (~ (real_le y0 (y1 y2 y3)))))) \/ (real_le (inf x0) y2)).
Definition term292 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : type1627, (fun y2 : real => fun y3 : type1627 => forall y4 : real, (forall y5 : real, (~ (@IN real y5 x0)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y3 y4 y5) x0) /\ (~ (real_le y2 (y3 y4 y5)))))) \/ (real_le (inf x0) y4)) y0 y1).
Definition term268 (x0 : real) (x1 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real -> real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) \/ (real_le (inf x1) y0)).
Definition term267 (x0 : real) (x1 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real -> real, (fun y2 : real => fun y3 : real -> real => (forall y4 : real, (~ (@IN real y4 x1)) \/ ((~ (real_le y4 y2)) \/ ((@IN real (y3 y4) x1) /\ (~ (real_le x0 (y3 y4)))))) \/ (real_le (inf x1) y2)) y0 y1).
Definition term222 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop (forall y0 : real, exists y1 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real y1 x1) /\ (~ (real_le x2 y1))))).
Definition term221 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x0)) \/ ((@IN real y3 x1) /\ (~ (real_le x2 y3))))) y0 y1).
Definition term384 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le x1 y0)) x2.
Definition term459 (x0 : real -> Prop) (x1 : real) := or (real_le (inf x0) x1).
Definition term116 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ((forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)) /\ (@IN real x1 x0)) /\ (~ (real_le (inf x0) x1)).
Definition term72 (x0 : real -> Prop) := exists y0 : real, ((exists y1 : real, forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) /\ (@IN real y0 x0)) /\ (~ (real_le (inf x0) y0)).
Definition term383 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (fun y0 : real => (((~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ (@IN real (x0 x2 x1 x3 y0) x2))) \/ (real_le (inf x2) x3)) /\ (((~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ (~ (real_le x1 (x0 x2 x1 x3 y0))))) \/ (real_le (inf x2) x3))) x4.
Definition term98 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x0 x1).
Definition term33 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => ((@IN real y0 x1) /\ ((real_le y0 x2) /\ (forall y1 : real, (@IN real y1 x1) -> real_le x0 y1))) -> real_le (inf x1) x2.
Definition term176 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term433 (x0 : real -> Prop) (x1 : real) := (real_le x1 x1) /\ (~ (real_le (inf x0) x1)).
Definition term196 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (fun y0 : real => (~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0)))) x4.
Definition term362 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (@IN real x4 x1)) \/ (((~ (real_le x4 x3)) \/ (@IN real (x0 x1 x2 x3 x4) x1)) /\ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4))))).
Definition term417 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term344 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := @eq Prop ((forall y0 : real, (~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x2 x1 x3 y0) x2) /\ (~ (real_le x1 (x0 x2 x1 x3 y0)))))) \/ (real_le (inf x2) x3)).
Definition term343 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := @eq Prop ((forall y0 : real, (fun y1 : real => (~ (@IN real y1 x2)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (x0 x2 x1 x3 y1) x2) /\ (~ (real_le x1 (x0 x2 x1 x3 y1)))))) y0) \/ (real_le (inf x2) x3)).
Definition term113 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((forall y0 : real, (~ (@IN real y0 x1)) \/ (real_le x0 y0)) /\ (@IN real x2 x1)) /\ (~ (real_le (inf x1) x2)).
Definition term175 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term57 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x0 x1).
Definition term45 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) /\ (@IN real x0 x1).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term454 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (real_le (inf x1) x4) \/ ((~ (@IN real x3 x1)) \/ ((~ (real_le x2 (x0 x1 x2 x4 x3))) \/ (~ (real_le x3 x4)))).
Definition term153 (x0 : real -> Prop) (x1 : Prop) := (forall y0 : real, x0 y0) \/ x1.
Definition term206 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => exists y1 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real y1 x1) /\ (~ (real_le x2 y1)))).
Definition term342 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := or (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (x0 x1 x2 x3 y1) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 y1)))))) y0).
Definition term166 (x0 : real) (x1 : real -> Prop) (x2 : real) := or (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x2 y2))))) y0).
Definition term456 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := @eq Prop ((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ ((~ (real_le x1 (x0 x3 x1 x4 x2))) \/ (real_le (inf x3) x4)))).
Definition term411 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := @eq Prop ((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ ((@IN real (x0 x3 x1 x4 x2) x3) \/ (real_le (inf x3) x4)))).
Definition term455 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (real_le x2 (x0 x1 x2 x4 x3))) \/ (~ (real_le x3 x4)).
Definition term316 := fun y0 : real -> Prop => exists y1 : type1625, (fun y2 : real -> Prop => fun y3 : type1625 => forall y4 : real, forall y5 : real, (forall y6 : real, (~ (@IN real y6 y2)) \/ ((~ (real_le y6 y5)) \/ ((@IN real (y3 y4 y5 y6) y2) /\ (~ (real_le y4 (y3 y4 y5 y6)))))) \/ (real_le (inf y2) y5)) y0 y1.
Definition term283 (x0 : real -> Prop) := forall y0 : real, exists y1 : type1627, (fun y2 : real => fun y3 : type1627 => forall y4 : real, (forall y5 : real, (~ (@IN real y5 x0)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y3 y4 y5) x0) /\ (~ (real_le y2 (y3 y4 y5)))))) \/ (real_le (inf x0) y4)) y0 y1.
Definition term281 (x0 : type1617) := forall y0 : real, exists y1 : type1627, x0 y0 y1.
Definition term280 (x0 : real -> Prop) := forall y0 : real, exists y1 : type1627, forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y1 y2 y3) x0) /\ (~ (real_le y0 (y1 y2 y3)))))) \/ (real_le (inf x0) y2).
Definition term258 (x0 : real) (x1 : real -> Prop) := forall y0 : real, exists y1 : real -> real, (fun y2 : real => fun y3 : real -> real => (forall y4 : real, (~ (@IN real y4 x1)) \/ ((~ (real_le y4 y2)) \/ ((@IN real (y3 y4) x1) /\ (~ (real_le x0 (y3 y4)))))) \/ (real_le (inf x1) y2)) y0 y1.
Definition term256 (x0 : type1618) := forall y0 : real, exists y1 : real -> real, x0 y0 y1.
Definition term255 (x0 : real) (x1 : real -> Prop) := forall y0 : real, exists y1 : real -> real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) \/ (real_le (inf x1) y0).
Definition term212 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x0)) \/ ((@IN real y3 x1) /\ (~ (real_le x2 y3))))) y0 y1.
Definition term210 (x0 : type1626) := forall y0 : real, exists y1 : real, x0 y0 y1.
Definition term207 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, exists y1 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real y1 x1) /\ (~ (real_le x2 y1)))).
Definition term20 := (forall y0 : real, real_le y0 y0) -> ~ (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2).
Definition term29 (x0 : real) (x1 : real -> Prop) := and (@IN real x0 x1).
Definition term25 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le x1 y0.
Definition term13 := (((~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False.
Definition term337 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x2)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (x0 x2 x1 x3 y1) x2) /\ (~ (real_le x1 (x0 x2 x1 x3 y1)))))) y0) \/ (real_le (inf x2) x3).
Definition term315 (x0 : real -> Prop) := exists y0 : type1625, (fun y1 : real -> Prop => fun y2 : type1625 => forall y3 : real, forall y4 : real, (forall y5 : real, (~ (@IN real y5 y1)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y2 y3 y4 y5) y1) /\ (~ (real_le y3 (y2 y3 y4 y5)))))) \/ (real_le (inf y1) y4)) x0 y0.
Definition term205 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := exists y0 : real, (~ (@IN real x0 x2)) \/ ((~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0)))).
Definition term158 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := or ((fun y0 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x2 y1))))) x3).
Definition term48 (x0 : real -> Prop) := fun y0 : real => ((exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) /\ (@IN real y0 x0)) -> real_le (inf x0) y0.
Definition term405 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (@IN real (x0 x2 x1 x4 x3) x2) \/ ((real_le (inf x2) x4) \/ (~ (real_le x3 x4))).
Definition term352 (x0 : type1018) (x1 : real) (x2 : real -> Prop) := fun y0 : real => forall y1 : real, ((~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ ((@IN real (x0 x2 x1 y0 y1) x2) /\ (~ (real_le x1 (x0 x2 x1 y0 y1)))))) \/ (real_le (inf x2) y0).
Definition term336 (x0 : type1018) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (x0 x1 y0 y1 y2) x1) /\ (~ (real_le y0 (x0 x1 y0 y1 y2)))))) \/ (real_le (inf x1) y1).
Definition term298 (x0 : type1625) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (x0 y0 y1 y2) x1) /\ (~ (real_le y0 (x0 y0 y1 y2)))))) \/ (real_le (inf x1) y1).
Definition term171 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (forall y2 : real, (~ (@IN real y2 x0)) \/ ((~ (real_le y2 y1)) \/ (exists y3 : real, (@IN real y3 x0) /\ (~ (real_le y0 y3))))) \/ (real_le (inf x0) y1).
Definition term144 (x0 : real) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, ((~ (@IN real y1 x1)) \/ ((~ (real_le y1 y0)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x0 y2))))) \/ (real_le (inf x1) y0).
Definition term54 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1).
Definition term42 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y0 y1.
Definition term35 (x0 : real) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, ((@IN real y1 x1) /\ ((real_le y1 y0) /\ (forall y2 : real, (@IN real y2 x1) -> real_le x0 y2))) -> real_le (inf x1) y0.
Definition term131 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (real_le x0 x1)) \/ (~ (forall y0 : real, (@IN real y0 x2) -> real_le x3 y0)).
Definition term333 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := (forall y0 : real, (~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x2 x1 x3 y0) x2) /\ (~ (real_le x1 (x0 x2 x1 x3 y0)))))) \/ (real_le (inf x2) x3).
Definition term271 (x0 : real) (x1 : type1627) (x2 : real -> Prop) (x3 : real) := (forall y0 : real, (~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x1 x3 y0) x2) /\ (~ (real_le x0 (x1 x3 y0)))))) \/ (real_le (inf x2) x3).
Definition term250 (x0 : real) (x1 : real -> real) (x2 : real -> Prop) (x3 : real) := (forall y0 : real, (~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x1 y0) x2) /\ (~ (real_le x0 (x1 y0)))))) \/ (real_le (inf x2) x3).
Definition term370 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4)))).
Definition term65 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term142 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => ((~ (@IN real y0 x1)) \/ ((~ (real_le y0 x2)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x0 y1))))) \/ (real_le (inf x1) x2).
Definition term452 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (real_le (inf x1) x4) \/ ((~ (real_le x2 (x0 x1 x2 x4 x3))) \/ (~ (real_le x3 x4))).
Definition term126 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (@IN real y0 x0) -> real_le x1 y0) x2).
Definition term477 (x0 : real -> Prop) (x1 : real) := (real_le (inf x0) x1) -> False.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term234 (x0 : real) (x1 : real -> Prop) (x2 : real) := (exists y0 : real -> real, forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x0 (y0 y1)))))) \/ (real_le (inf x1) x2).
Definition term19 := (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False.
Definition term312 (x0 : real -> Prop) (x1 : type1625) := (fun y0 : real -> Prop => fun y1 : type1625 => forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y1 y2 y3 y4) y0) /\ (~ (real_le y2 (y1 y2 y3 y4)))))) \/ (real_le (inf y0) y3)) x0 x1.
Definition term236 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term444 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term177 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term79 := fun y0 : real -> Prop => exists y1 : real, ((exists y2 : real, forall y3 : real, (~ (@IN real y3 y0)) \/ (real_le y2 y3)) /\ (@IN real y1 y0)) /\ (~ (real_le (inf y0) y1)).
Definition term462 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := ~ ((~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4))))).
Definition term26 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le x1 y0.
Definition term424 (x0 : real) (x1 : real -> Prop) (x2 : real) := ~ ((~ (real_le x0 x2)) \/ (real_le (inf x1) x2)).
Definition term422 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term472 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := ((@IN real x2 x3) /\ ((real_le x2 x4) /\ (real_le x1 (x0 x3 x1 x4 x2)))) -> real_le (inf x3) x4.
Definition term260 (x0 : real) (x1 : real -> Prop) := fun y0 : real => fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) \/ (real_le (inf x1) y0).
Definition term40 := fun y0 : real => real_le y0 y0.
Definition term348 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := ((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ ((@IN real (x0 x3 x1 x4 x2) x3) /\ (~ (real_le x1 (x0 x3 x1 x4 x2)))))) \/ (real_le (inf x3) x4).
Definition term49 (x0 : real -> Prop) := forall y0 : real, ((exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) /\ (@IN real y0 x0)) -> real_le (inf x0) y0.
Definition term345 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := or ((fun y0 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x1 x2 x3 y0) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 y0)))))) x4).
Definition term474 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := (@IN real x3 x1) /\ ((real_le x3 x3) /\ (real_le x2 (x0 x1 x2 x3 x3))).
Definition term9 := (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> False.
Definition term341 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (x0 x1 x2 x3 y1) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 y1)))))) y0.
Definition term164 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x2 y2))))) y0.
Definition term436 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) := @IN real (x0 x3 x1 x2 x2) x3.
Definition term279 (x0 : real -> Prop) := fun y0 : real => exists y1 : type1627, forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y1 y2 y3) x0) /\ (~ (real_le y0 (y1 y2 y3)))))) \/ (real_le (inf x0) y2).
Definition term406 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (~ (@IN real x3 x2)) \/ ((@IN real (x0 x2 x1 x4 x3) x2) \/ ((real_le (inf x2) x4) \/ (~ (real_le x3 x4)))).
Definition term251 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real -> real => ((fun y1 : real -> real => forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x2)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) y0) \/ (real_le (inf x1) x2).
Definition term304 := fun y0 : real -> Prop => exists y1 : type1625, forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y1 y2 y3 y4) y0) /\ (~ (real_le y2 (y1 y2 y3 y4)))))) \/ (real_le (inf y0) y3).
Definition term360 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real) (x4 : real -> Prop) := @IN real (x0 x4 x1 x2 x3) x4.
Definition term437 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) := (~ (@IN real (x0 x3 x1 x2 x2) x3)) -> @IN real (x0 x3 x1 x2 x2) x3.
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term110 (x0 : real) (x1 : real -> Prop) (x2 : real) := and ((fun y0 : real => (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x0 x1)) x2).
Definition term249 (x0 : real) (x1 : real -> real) (x2 : real -> Prop) (x3 : real) := ((fun y0 : real -> real => forall y1 : real, (~ (@IN real y1 x2)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (y0 y1) x2) /\ (~ (real_le x0 (y0 y1)))))) x1) \/ (real_le (inf x2) x3).
Definition term14 := (((~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False) -> ((~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False) -> (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False.
Definition term254 (x0 : real) (x1 : real -> Prop) := fun y0 : real => exists y1 : real -> real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) \/ (real_le (inf x1) y0).
Definition term31 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := imp ((@IN real x0 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x3 y0))).
Definition term130 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term438 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) := ~ (@IN real (x0 x3 x1 x2 x2) x3).
Definition term371 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := fun y0 : real => (((~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ (@IN real (x0 x2 x1 x3 y0) x2))) \/ (real_le (inf x2) x3)) /\ (((~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ (~ (real_le x1 (x0 x2 x1 x3 y0))))) \/ (real_le (inf x2) x3)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term93 (x0 : real -> Prop) (x1 : real) := and ((fun y0 : real => forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)) x1).
Definition term87 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)) x1.
Definition term349 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := fun y0 : real => ((fun y1 : real => (~ (@IN real y1 x2)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (x0 x2 x1 x3 y1) x2) /\ (~ (real_le x1 (x0 x2 x1 x3 y1)))))) y0) \/ (real_le (inf x2) x3).
Definition term427 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term423 (x0 : real) (x1 : real -> Prop) := and (~ (~ (@IN real x0 x1))).
Definition term431 (x0 : real) (x1 : real -> Prop) (x2 : real) := imp ((@IN real x0 x1) /\ ((real_le x0 x2) /\ (~ (real_le (inf x1) x2)))).
Definition term138 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := or (~ ((@IN real x0 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x3 y0)))).
Definition term101 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, (forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)) /\ (@IN real x1 x0)) /\ (~ (real_le (inf x0) x1)).
Definition term52 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le x1 y0).
Definition term30 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (@IN real x0 x2) /\ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x3 y0)).
Definition term334 (x0 : type1018) (x1 : real) (x2 : real -> Prop) := fun y0 : real => (forall y1 : real, (~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ ((@IN real (x0 x2 x1 y0 y1) x2) /\ (~ (real_le x1 (x0 x2 x1 y0 y1)))))) \/ (real_le (inf x2) y0).
Definition term273 (x0 : real) (x1 : type1627) (x2 : real -> Prop) := fun y0 : real => (forall y1 : real, (~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ ((@IN real (x1 y0 y1) x2) /\ (~ (real_le x0 (x1 y0 y1)))))) \/ (real_le (inf x2) y0).
Definition term169 (x0 : real) (x1 : real -> Prop) := fun y0 : real => (forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 y0)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x0 y2))))) \/ (real_le (inf x1) y0).
Definition term299 (x0 : real -> Prop) (x1 : type1625) := forall y0 : real, (fun y1 : real => fun y2 : type1627 => forall y3 : real, (forall y4 : real, (~ (@IN real y4 x0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y2 y3 y4) x0) /\ (~ (real_le y1 (y2 y3 y4)))))) \/ (real_le (inf x0) y3)) y0 (x1 y0).
Definition term168 (x0 : real) (x1 : real -> Prop) (x2 : real) := (forall y0 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x2)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x0 y1))))) \/ (real_le (inf x1) x2).
Definition term382 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := (fun y0 : real => forall y1 : real, (((~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ (@IN real (x0 x2 x1 y0 y1) x2))) \/ (real_le (inf x2) y0)) /\ (((~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ (~ (real_le x1 (x0 x2 x1 y0 y1))))) \/ (real_le (inf x2) y0))) x3.
Definition term95 (x0 : real) (x1 : real) (x2 : real -> Prop) := ((fun y0 : real => forall y1 : real, (~ (@IN real y1 x2)) \/ (real_le y0 y1)) x0) /\ (@IN real x1 x2).
Definition term18 := imp (forall y0 : real, real_le y0 y0).
Definition term324 (x0 : type1018) := forall y0 : real -> Prop, (fun y1 : real -> Prop => fun y2 : type1625 => forall y3 : real, forall y4 : real, (forall y5 : real, (~ (@IN real y5 y1)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y2 y3 y4 y5) y1) /\ (~ (real_le y3 (y2 y3 y4 y5)))))) \/ (real_le (inf y1) y4)) y0 (x0 y0).
Definition term178 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term8 := forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1.
Definition term83 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term434 (x0 : real -> Prop) (x1 : real) := (@IN real x1 x0) /\ ((real_le x1 x1) /\ (~ (real_le (inf x0) x1))).
Definition term58 (x0 : real -> Prop) (x1 : real) := ~ (real_le (inf x0) x1).
Definition term32 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := ((@IN real x0 x2) /\ ((real_le x0 x3) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x1 y0))) -> real_le (inf x2) x3.
Definition term78 := fun y0 : real -> Prop => ~ ((fun y1 : real -> Prop => forall y2 : real, ((exists y3 : real, forall y4 : real, (@IN real y4 y1) -> real_le y3 y4) /\ (@IN real y2 y1)) -> real_le (inf y1) y2) y0).
Definition term365 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4))).
Definition term264 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real -> real => (fun y1 : real => fun y2 : real -> real => (forall y3 : real, (~ (@IN real y3 x1)) \/ ((~ (real_le y3 y1)) \/ ((@IN real (y2 y3) x1) /\ (~ (real_le x0 (y2 y3)))))) \/ (real_le (inf x1) y1)) x2 y0.
Definition term466 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := ~ (~ (real_le x2 (x0 x1 x2 x3 x4))).
Definition term202 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (~ (@IN real x0 x2)) \/ ((~ (real_le x0 x1)) \/ ((@IN real x4 x2) /\ (~ (real_le x3 x4)))).
Definition term165 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x2 y1)))).
Definition term414 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (@IN real (x0 x3 x1 x4 x2) x3) \/ ((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ (real_le (inf x3) x4))).
Definition term368 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ (@IN real (x0 x3 x1 x4 x2) x3))) \/ (real_le (inf x3) x4)) /\ (((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ (~ (real_le x1 (x0 x3 x1 x4 x2))))) \/ (real_le (inf x3) x4)).
Definition term375 (x0 : type1018) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, forall y2 : real, (((~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ (@IN real (x0 x1 y0 y1 y2) x1))) \/ (real_le (inf x1) y1)) /\ (((~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ (~ (real_le y0 (x0 x1 y0 y1 y2))))) \/ (real_le (inf x1) y1)).
Definition term354 (x0 : type1018) (x1 : real -> Prop) := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (x0 x1 y0 y1 y2) x1) /\ (~ (real_le y0 (x0 x1 y0 y1 y2)))))) \/ (real_le (inf x1) y1).
Definition term146 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (@IN real y2 x0)) \/ ((~ (real_le y2 y1)) \/ (exists y3 : real, (@IN real y3 x0) /\ (~ (real_le y0 y3))))) \/ (real_le (inf x0) y1).
Definition term37 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, forall y2 : real, ((@IN real y2 x0) /\ ((real_le y2 y1) /\ (forall y3 : real, (@IN real y3 x0) -> real_le y0 y3))) -> real_le (inf x0) y1.
Definition term379 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term301 (x0 : real -> Prop) := fun y0 : type1625 => forall y1 : real, (fun y2 : real => fun y3 : type1627 => forall y4 : real, (forall y5 : real, (~ (@IN real y5 x0)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y3 y4 y5) x0) /\ (~ (real_le y2 (y3 y4 y5)))))) \/ (real_le (inf x0) y4)) y1 (y0 y1).
Definition term277 (x0 : real) (x1 : real -> Prop) := fun y0 : type1627 => forall y1 : real, (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y1)) \/ ((@IN real (y0 y1 y2) x1) /\ (~ (real_le x0 (y0 y1 y2)))))) \/ (real_le (inf x1) y1).
Definition term276 (x0 : real) (x1 : real -> Prop) := fun y0 : type1627 => forall y1 : real, (fun y2 : real => fun y3 : real -> real => (forall y4 : real, (~ (@IN real y4 x1)) \/ ((~ (real_le y4 y2)) \/ ((@IN real (y3 y4) x1) /\ (~ (real_le x0 (y3 y4)))))) \/ (real_le (inf x1) y2)) y1 (y0 y1).
Definition term231 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real -> real => forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x2 (y0 y1))))).
Definition term230 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x0)) \/ ((@IN real y3 x1) /\ (~ (real_le x2 y3))))) y1 (y0 y1).
Definition term50 := fun y0 : real -> Prop => forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1.
Definition term464 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := ~ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4)))).
Definition term394 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ ((~ (real_le x1 (x0 x3 x1 x4 x2))) \/ (real_le (inf x3) x4))).
Definition term269 (x0 : real) (x1 : real -> Prop) (x2 : type1627) (x3 : real) := (fun y0 : real => fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) \/ (real_le (inf x1) y0)) x3 (x2 x3).
Definition term244 (x0 : real) (x1 : real -> Prop) (x2 : real) := or (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x2 (y1 y2)))))) y0).
Definition term181 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term223 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) (x4 : real) := (fun y0 : real => fun y1 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real y1 x1) /\ (~ (real_le x2 y1))))) x4 (x3 x4).
Definition term328 := exists y0 : type1018, forall y1 : real -> Prop, forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y1)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y0 y1 y2 y3 y4) y1) /\ (~ (real_le y2 (y0 y1 y2 y3 y4)))))) \/ (real_le (inf y1) y3).
Definition term303 (x0 : real -> Prop) := exists y0 : type1625, forall y1 : real, forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y0 y1 y2 y3) x0) /\ (~ (real_le y1 (y0 y1 y2 y3)))))) \/ (real_le (inf x0) y2).
Definition term179 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (real_le x0 x1)) \/ (exists y0 : real, (fun y1 : real => (@IN real y1 x2) /\ (~ (real_le x3 y1))) y0).
Definition term97 (x0 : real) (x1 : real -> Prop) := fun y0 : real => ((fun y1 : real => forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)) y0) /\ (@IN real x0 x1).
Definition term46 (x0 : real) (x1 : real -> Prop) := imp ((exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y0 y1) /\ (@IN real x0 x1)).
Definition term311 (x0 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : type1625 => forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y1 y2 y3 y4) y0) /\ (~ (real_le y2 (y1 y2 y3 y4)))))) \/ (real_le (inf y0) y3)) x0.
Definition term129 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (~ (real_le x1 y0)).
Definition term133 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := ~ ((real_le x0 x1) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x3 y0)).
Definition term112 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((fun y0 : real => (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x2 x1)) x0) /\ (~ (real_le (inf x1) x2)).
Definition term240 (x0 : real) (x1 : real -> Prop) (x2 : real) := exists y0 : real -> real, ((fun y1 : real -> real => forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x2)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) y0) \/ (real_le (inf x1) x2).
Definition term53 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le x1 y0).
Definition term448 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := ~ (real_le x2 (x0 x1 x2 x3 x3)).
Definition term102 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) /\ (@IN real x1 x0)) y0) /\ (~ (real_le (inf x0) x1)).
Definition term329 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ ((@IN real (x0 x1 x2 x3 x4) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 x4))))).
Definition term225 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) (x4 : real) := (~ (@IN real x4 x1)) \/ ((~ (real_le x4 x0)) \/ ((@IN real (x3 x4) x1) /\ (~ (real_le x2 (x3 x4))))).
Definition term285 (x0 : real -> Prop) := fun y0 : real => fun y1 : type1627 => forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y1 y2 y3) x0) /\ (~ (real_le y0 (y1 y2 y3)))))) \/ (real_le (inf x0) y2).
Definition term391 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := (~ (@IN real x2 x3)) \/ (((~ (real_le x2 x4)) \/ (~ (real_le x1 (x0 x3 x1 x4 x2)))) \/ (real_le (inf x3) x4)).
Definition term310 := fun y0 : real -> Prop => fun y1 : type1625 => forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y1 y2 y3 y4) y0) /\ (~ (real_le y2 (y1 y2 y3 y4)))))) \/ (real_le (inf y0) y3).
Definition term107 (x0 : real) (x1 : real -> Prop) := and (exists y0 : real, (fun y1 : real => (forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)) /\ (@IN real x0 x1)) y0).
Definition term90 (x0 : real -> Prop) := and (exists y0 : real, (fun y1 : real => forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) y0).
Definition term358 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (~ (real_le x4 x3)) \/ ((@IN real (x0 x1 x2 x3 x4) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 x4)))).
Definition term27 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term272 (x0 : real) (x1 : real -> Prop) (x2 : type1627) := fun y0 : real => (fun y1 : real => fun y2 : real -> real => (forall y3 : real, (~ (@IN real y3 x1)) \/ ((~ (real_le y3 y1)) \/ ((@IN real (y2 y3) x1) /\ (~ (real_le x0 (y2 y3)))))) \/ (real_le (inf x1) y1)) y0 (x2 y0).
Definition term403 (x0 : real -> Prop) (x1 : real) (x2 : real) := (real_le (inf x0) x2) \/ (~ (real_le x1 x2)).
Definition term182 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le x1 y0))) x2.
Definition term160 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => ((fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x0 y2))))) y0) \/ (real_le (inf x1) x2).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term322 (x0 : type1018) := fun y0 : real -> Prop => (fun y1 : real -> Prop => fun y2 : type1625 => forall y3 : real, forall y4 : real, (forall y5 : real, (~ (@IN real y5 y1)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y2 y3 y4 y5) y1) /\ (~ (real_le y3 (y2 y3 y4 y5)))))) \/ (real_le (inf y1) y4)) y0 (x0 y0).
Definition term395 (x0 : real) (x1 : real -> Prop) := (~ (@IN real x0 x1)) -> @IN real x0 x1.
Definition term127 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) -> real_le x1 y1) y0).
Definition term70 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => ((exists y2 : real, forall y3 : real, (@IN real y3 x0) -> real_le y2 y3) /\ (@IN real y1 x0)) -> real_le (inf x0) y1) y0).
Definition term314 (x0 : real -> Prop) := fun y0 : type1625 => (fun y1 : real -> Prop => fun y2 : type1625 => forall y3 : real, forall y4 : real, (forall y5 : real, (~ (@IN real y5 y1)) \/ ((~ (real_le y5 y4)) \/ ((@IN real (y2 y3 y4 y5) y1) /\ (~ (real_le y3 (y2 y3 y4 y5)))))) \/ (real_le (inf y1) y4)) x0 y0.
Definition term224 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) (x4 : real) := (fun y0 : real => (~ (@IN real x4 x1)) \/ ((~ (real_le x4 x0)) \/ ((@IN real y0 x1) /\ (~ (real_le x2 y0))))) (x3 x4).
Definition term469 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := (@IN real x4 x1) /\ ((real_le x4 x3) /\ (real_le x2 (x0 x1 x2 x3 x4))).
Definition term408 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x1 x0)) \/ ((real_le (inf x0) x2) \/ (~ (real_le x1 x2))).
Definition term335 (x0 : type1018) (x1 : real) (x2 : real -> Prop) := forall y0 : real, (forall y1 : real, (~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ ((@IN real (x0 x2 x1 y0 y1) x2) /\ (~ (real_le x1 (x0 x2 x1 y0 y1)))))) \/ (real_le (inf x2) y0).
Definition term296 (x0 : type1625) (x1 : real) (x2 : real -> Prop) := forall y0 : real, (forall y1 : real, (~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ ((@IN real (x0 x1 y0 y1) x2) /\ (~ (real_le x1 (x0 x1 y0 y1)))))) \/ (real_le (inf x2) y0).
Definition term275 (x0 : real) (x1 : type1627) (x2 : real -> Prop) := forall y0 : real, (forall y1 : real, (~ (@IN real y1 x2)) \/ ((~ (real_le y1 y0)) \/ ((@IN real (x1 y0 y1) x2) /\ (~ (real_le x0 (x1 y0 y1)))))) \/ (real_le (inf x2) y0).
Definition term170 (x0 : real) (x1 : real -> Prop) := forall y0 : real, (forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 y0)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x0 y2))))) \/ (real_le (inf x1) y0).
Definition term155 (x0 : real) (x1 : real -> Prop) (x2 : real) := (forall y0 : real, (fun y1 : real => (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ (exists y2 : real, (@IN real y2 x1) /\ (~ (real_le x0 y2))))) y0) \/ (real_le (inf x1) x2).
Definition term404 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real) (x4 : real -> Prop) := or (@IN real (x0 x4 x1 x2 x3) x4).
Definition term103 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ((fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) /\ (@IN real x1 x0)) y0) /\ (~ (real_le (inf x0) x1)).
Definition term24 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x2 x0) -> real_le x1 x2.
Definition term457 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := @eq Prop ((real_le (inf x1) x4) \/ ((~ (@IN real x3 x1)) \/ ((~ (real_le x2 (x0 x1 x2 x4 x3))) \/ (~ (real_le x3 x4))))).
Definition term157 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (fun y0 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x2 y1))))) x3.
Definition term369 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real) (x4 : real -> Prop) := (~ (@IN real x3 x4)) \/ ((~ (real_le x3 x2)) \/ (@IN real (x0 x4 x1 x2 x3) x4)).
Definition term238 (x0 : type1028) (x1 : Prop) := exists y0 : real -> real, (x0 y0) \/ x1.
Definition term440 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((~ (@IN real x2 x0)) \/ (real_le x1 x2)).
Definition term190 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := fun y0 : real => (~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0))).
Definition term74 (x0 : type1022) := exists y0 : real -> Prop, ~ (x0 y0).
Definition term319 (x0 : type1018) (x1 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : type1625 => forall y2 : real, forall y3 : real, (forall y4 : real, (~ (@IN real y4 y0)) \/ ((~ (real_le y4 y3)) \/ ((@IN real (y1 y2 y3 y4) y0) /\ (~ (real_le y2 (y1 y2 y3 y4)))))) \/ (real_le (inf y0) y3)) x1 (x0 x1).
Definition term241 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := (fun y0 : real -> real => forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x0)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x2 (y0 y1)))))) x3.
Definition term132 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (real_le x0 x1)) \/ (exists y0 : real, (@IN real y0 x2) /\ (~ (real_le x3 y0))).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term204 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := fun y0 : real => (~ (@IN real x0 x2)) \/ ((~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0)))).
Definition term435 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) := ((@IN real x2 x3) /\ ((real_le x2 x2) /\ (~ (real_le (inf x3) x2)))) -> @IN real (x0 x3 x1 x2 x2) x3.
Definition term364 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real) (x4 : real -> Prop) := (~ (real_le x3 x2)) \/ (@IN real (x0 x4 x1 x2 x3) x4).
Definition term143 (x0 : real) (x1 : real -> Prop) (x2 : real) := forall y0 : real, ((~ (@IN real y0 x1)) \/ ((~ (real_le y0 x2)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x0 y1))))) \/ (real_le (inf x1) x2).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term215 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real) := (fun y0 : real => fun y1 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real y1 x1) /\ (~ (real_le x2 y1))))) x3.
Definition term56 (x0 : real -> Prop) := and (exists y0 : real, forall y1 : real, (~ (@IN real y1 x0)) \/ (real_le y0 y1)).
Definition term44 (x0 : real -> Prop) := and (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y0 y1).
Definition term156 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ (exists y1 : real, (@IN real y1 x1) /\ (~ (real_le x2 y1)))).
Definition term104 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x0 x1)) x2.
Definition term136 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (@IN real x0 x2)) \/ ((~ (real_le x0 x1)) \/ (exists y0 : real, (@IN real y0 x2) /\ (~ (real_le x3 y0)))).
Definition term193 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ (@IN real x0 x2)) \/ (exists y0 : real, (fun y1 : real => (~ (real_le x0 x1)) \/ ((@IN real y1 x2) /\ (~ (real_le x3 y1)))) y0).
Definition term114 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((fun y1 : real => (forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) /\ (@IN real x1 x0)) y0) /\ (~ (real_le (inf x0) x1)).
Definition term23 (x0 : real -> Prop) (x1 : real) := real_le (inf x0) x1.
Definition term410 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) (x4 : real) := (@IN real (x0 x2 x1 x4 x3) x2) \/ ((real_le (inf x2) x4) \/ ((~ (@IN real x3 x2)) \/ (~ (real_le x3 x4)))).
Definition term366 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := or (((~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ (@IN real (x0 x1 x2 x3 x4) x1))) /\ ((~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4)))))).
Definition term351 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := forall y0 : real, ((~ (@IN real y0 x2)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x2 x1 x3 y0) x2) /\ (~ (real_le x1 (x0 x2 x1 x3 y0)))))) \/ (real_le (inf x2) x3).
Definition term209 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term121 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((@IN real x2 x0) -> real_le x1 x2).
Definition term134 (x0 : real) (x1 : real -> Prop) := or (~ (@IN real x0 x1)).
Definition term320 (x0 : type1018) (x1 : real -> Prop) := (fun y0 : type1625 => forall y1 : real, forall y2 : real, (forall y3 : real, (~ (@IN real y3 x1)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y0 y1 y2 y3) x1) /\ (~ (real_le y1 (y0 y1 y2 y3)))))) \/ (real_le (inf x1) y2)) (x0 x1).
Definition term287 (x0 : real -> Prop) (x1 : real) (x2 : type1627) := (fun y0 : real => fun y1 : type1627 => forall y2 : real, (forall y3 : real, (~ (@IN real y3 x0)) \/ ((~ (real_le y3 y2)) \/ ((@IN real (y1 y2 y3) x0) /\ (~ (real_le y0 (y1 y2 y3)))))) \/ (real_le (inf x0) y2)) x1 x2.
Definition term447 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := (~ (real_le x2 (x0 x1 x2 x3 x3))) -> real_le x2 (x0 x1 x2 x3 x3).
Definition term346 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := or ((~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ ((@IN real (x0 x1 x2 x3 x4) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 x4)))))).
Definition term252 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real -> real => (forall y1 : real, (~ (@IN real y1 x1)) \/ ((~ (real_le y1 x2)) \/ ((@IN real (y0 y1) x1) /\ (~ (real_le x0 (y0 y1)))))) \/ (real_le (inf x1) x2).
Definition term11 := (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)) -> (forall y0 : real, real_le y0 y0) -> (forall y0 : real -> Prop, forall y1 : real, forall y2 : real, forall y3 : real, ((@IN real y3 y0) /\ ((real_le y3 y2) /\ (forall y4 : real, (@IN real y4 y0) -> real_le y1 y4))) -> real_le (inf y0) y2) -> False.
Definition term100 (x0 : real) (x1 : real -> Prop) := and (exists y0 : real, (forall y1 : real, (~ (@IN real y1 x1)) \/ (real_le y0 y1)) /\ (@IN real x0 x1)).
Definition term262 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := (fun y0 : real => fun y1 : real -> real => (forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 y0)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) \/ (real_le (inf x1) y0)) x2 x3.
Definition term330 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := fun y0 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x3)) \/ ((@IN real (x0 x1 x2 x3 y0) x1) /\ (~ (real_le x2 (x0 x1 x2 x3 y0))))).
Definition term227 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : real -> real) := fun y0 : real => (~ (@IN real y0 x1)) \/ ((~ (real_le y0 x0)) \/ ((@IN real (x3 y0) x1) /\ (~ (real_le x2 (x3 y0))))).
Definition term363 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) (x4 : real) := ((~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ (@IN real (x0 x1 x2 x3 x4) x1))) /\ ((~ (@IN real x4 x1)) \/ ((~ (real_le x4 x3)) \/ (~ (real_le x2 (x0 x1 x2 x3 x4))))).
Definition term388 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := ((~ (real_le x2 x4)) \/ (@IN real (x0 x3 x1 x4 x2) x3)) \/ (real_le (inf x3) x4).
Definition term191 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := exists y0 : real, (~ (real_le x0 x1)) \/ ((@IN real y0 x2) /\ (~ (real_le x3 y0))).
Definition term21 := imp (~ (forall y0 : real -> Prop, forall y1 : real, ((exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) /\ (@IN real y1 y0)) -> real_le (inf y0) y1)).
Definition term400 (x0 : Prop) := x0 -> ~ x0.
Definition term239 (x0 : real) (x1 : real -> Prop) (x2 : real) := (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (~ (@IN real y2 x1)) \/ ((~ (real_le y2 x2)) \/ ((@IN real (y1 y2) x1) /\ (~ (real_le x0 (y1 y2)))))) y0) \/ (real_le (inf x1) x2).
Definition term446 (x0 : type1018) (x1 : real -> Prop) (x2 : real) (x3 : real) := real_le x2 (x0 x1 x2 x3 x3).
Definition term385 (x0 : type1018) (x1 : real) (x2 : real) (x3 : real -> Prop) (x4 : real) := ((~ (@IN real x2 x3)) \/ ((~ (real_le x2 x4)) \/ (~ (real_le x1 (x0 x3 x1 x4 x2))))) \/ (real_le (inf x3) x4).
Definition term338 (x0 : type1018) (x1 : real) (x2 : real -> Prop) (x3 : real) := forall y0 : real, ((fun y1 : real => (~ (@IN real y1 x2)) \/ ((~ (real_le y1 x3)) \/ ((@IN real (x0 x2 x1 x3 y1) x2) /\ (~ (real_le x1 (x0 x2 x1 x3 y1)))))) y0) \/ (real_le (inf x2) x3).
Definition term443 (x0 : real) (x1 : real -> Prop) := imp (~ (~ (@IN real x0 x1))).
Definition term89 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => forall y2 : real, (~ (@IN real y2 x0)) \/ (real_le y1 y2)) y0.
Definition term140 (x0 : real) (x1 : real) (x2 : real -> Prop) (x3 : real) := (~ ((@IN real x0 x2) /\ ((real_le x0 x3) /\ (forall y0 : real, (@IN real y0 x2) -> real_le x1 y0)))) \/ (real_le (inf x2) x3).
Definition term85 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, (fun y1 : real => forall y2 : real, (~ (@IN real y2 x1)) \/ (real_le y1 y2)) y0) /\ (@IN real x0 x1).
Definition term402 (x0 : real) (x1 : real -> Prop) (x2 : real) := (~ (real_le x0 x2)) \/ (real_le (inf x1) x2).
