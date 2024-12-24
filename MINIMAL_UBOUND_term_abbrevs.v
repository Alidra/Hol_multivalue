Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term213 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ ((~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0))).
Definition term331 (x0 : nat -> Prop) := Peano.le (minimal x0).
Definition term21 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term442 (x0 : nat -> Prop) (x1 : nat) := (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0)) x1) -> False.
Definition term101 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term46 (x0 : type993) := ~ (all x0).
Definition term37 (x0 : nat -> Prop) := ~ (all x0).
Definition term443 := (~ False) -> False.
Definition term119 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term388 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((~ (@I (nat -> Prop) x1 x0)) \/ (forall y0 : nat, (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0))))).
Definition term387 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((~ (@I (nat -> Prop) x1 x0)) \/ (forall y0 : nat, (fun y1 : nat => (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y1)))) y0)).
Definition term378 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term286 (x0 : nat) (x1 : nat -> Prop) := Peano.lt x0 (@I ((nat -> Prop) -> nat) minimal x1).
Definition term73 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term326 (x0 : type994) (x1 : nat -> Prop) := (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) x0 x1)) \/ ((~ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1))) \/ ((@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 x1)) (@I ((nat -> Prop) -> nat) minimal x1)) /\ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) x0 x1)))).
Definition term31 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) -> Peano.le (minimal x0) y0.
Definition term51 := fun y0 : nat -> Prop => ~ ((fun y1 : nat -> Prop => forall y2 : nat, (y1 y2) -> Peano.le (minimal y1) y2) y0).
Definition term126 (x0 : nat -> Prop) (x1 : nat) := ~ ((Peano.lt x1 (minimal x0)) -> ~ (x0 x1)).
Definition term161 := fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1))).
Definition term93 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term70 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term367 (x0 : nat -> Prop) := forall y0 : nat, (fun y1 : nat => ~ (@I (nat -> Prop) x0 y1)) y0.
Definition term185 (x0 : nat -> Prop) := ~ (x0 (minimal x0)).
Definition term53 := exists y0 : nat -> Prop, exists y1 : nat, (y0 y1) /\ (~ (Peano.le (minimal y0) y1)).
Definition term356 (x0 : nat -> Prop) := fun y0 : nat => (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))).
Definition term215 (x0 : nat -> Prop) := @eq Prop ((fun y0 : Prop => y0 = (exists y1 : nat, (x0 y1) \/ ((~ (x0 (minimal x0))) \/ ((Peano.lt y1 (minimal x0)) /\ (x0 y1))))) ((exists y0 : nat, x0 y0) \/ (exists y0 : nat, (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0))))).
Definition term426 (x0 : Prop) := ~ (~ x0).
Definition term234 (x0 : type994) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => fun y1 : nat => (y0 y1) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt y1 (minimal y0)) /\ (y0 y1)))) x1 (x0 x1).
Definition term437 (x0 : nat) (x1 : nat) := (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le x1) x0) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) x1).
Definition term268 (x0 : nat) (x1 : nat) := (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) x0) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le x0) x1).
Definition term192 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (minimal x0))) \/ ((Peano.lt x1 (minimal x0)) /\ (x0 x1)).
Definition term332 (x0 : nat -> Prop) := Peano.le (@I ((nat -> Prop) -> nat) minimal x0).
Definition term278 (x0 : nat) (x1 : nat) := (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) x0)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le x0) x1)).
Definition term24 := fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1))).
Definition term48 := exists y0 : nat -> Prop, ~ ((fun y1 : nat -> Prop => forall y2 : nat, (y1 y2) -> Peano.le (minimal y1) y2) y0).
Definition term372 (x0 : nat -> Prop) (x1 : nat) := or (~ (@I (nat -> Prop) x0 x1)).
Definition term151 (x0 : nat -> Prop) := and ((exists y0 : nat, x0 y0) \/ (~ ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))))).
Definition term19 (x0 : nat -> Prop) := and (x0 (minimal x0)).
Definition term244 := and (exists y0 : type994, forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1))))).
Definition term79 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term276 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term341 (x0 : nat -> Prop) (x1 : nat) := (@I (nat -> Prop) x0 x1) /\ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0)) x1)).
Definition term439 (x0 : nat) (x1 : nat) := (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) x0)) -> @I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le x0) x1.
Definition term230 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat -> Prop => fun y2 : nat => (y1 y2) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt y2 (minimal y1)) /\ (y1 y2)))) x0 y0.
Definition term391 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (@I (nat -> Prop) x1 x0)) \/ ((fun y1 : nat => (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y1)))) y0).
Definition term299 (x0 : nat -> Prop) := (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ (forall y0 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))).
Definition term368 (x0 : nat -> Prop) := or (forall y0 : nat, (fun y1 : nat => ~ (@I (nat -> Prop) x0 y1)) y0).
Definition term425 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (@I (nat -> Prop) x1 x0))) /\ (~ (~ (@I (nat -> Prop) x1 x2))).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term136 (x0 : nat -> Prop) := fun y0 : nat => (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)).
Definition term405 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, forall y2 : nat, ((~ (@I (nat -> Prop) y0 y1)) \/ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0))) /\ ((~ (@I (nat -> Prop) y0 y1)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y2) (@I ((nat -> Prop) -> nat) minimal y0))) \/ (~ (@I (nat -> Prop) y0 y2))))) x0.
Definition term138 (x0 : nat -> Prop) := or (~ (x0 (minimal x0))).
Definition term379 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term262 := fun y0 : type994 => ((fun y1 : type994 => forall y2 : nat -> Prop, (y2 (y1 y2)) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt (y1 y2) (minimal y2)) /\ (y2 (y1 y2))))) y0) /\ (forall y1 : nat -> Prop, (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))).
Definition term403 := fun y0 : nat -> Prop => forall y1 : nat, forall y2 : nat, ((~ (@I (nat -> Prop) y0 y1)) \/ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0))) /\ ((~ (@I (nat -> Prop) y0 y1)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y2) (@I ((nat -> Prop) -> nat) minimal y0))) \/ (~ (@I (nat -> Prop) y0 y2)))).
Definition term396 := fun y0 : nat -> Prop => forall y1 : nat, forall y2 : nat, (~ (@I (nat -> Prop) y0 y1)) \/ ((@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y2) (@I ((nat -> Prop) -> nat) minimal y0))) \/ (~ (@I (nat -> Prop) y0 y2)))).
Definition term127 (x0 : nat) (x1 : nat -> Prop) := Peano.lt x0 (minimal x1).
Definition term34 (x0 : nat -> Prop) (x1 : nat) := ~ ((x0 x1) -> Peano.le (minimal x0) x1).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term94 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term71 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term284 := (forall y0 : nat, forall y1 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) y1)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y1) y0))) /\ (forall y0 : nat, forall y1 : nat, (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) y1) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y1) y0)).
Definition term112 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term63 (x0 : nat) := forall y0 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term430 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp (~ ((~ (@I (nat -> Prop) x1 x0)) \/ (~ (@I (nat -> Prop) x1 x2)))).
Definition term318 (x0 : type994) (x1 : nat -> Prop) := (Peano.lt (x0 x1) (minimal x1)) /\ (x1 (x0 x1)).
Definition term193 (x0 : nat -> Prop) := fun y0 : nat => (~ (x0 (minimal x0))) \/ ((fun y1 : nat => (Peano.lt y1 (minimal x0)) /\ (x0 y1)) y0).
Definition term316 (x0 : type994) (x1 : nat -> Prop) := and (Peano.lt (x0 x1) (minimal x1)).
Definition term270 (x0 : nat) := forall y0 : nat, (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) y0) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y0) x0).
Definition term191 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (minimal x0))) \/ ((fun y0 : nat => (Peano.lt y0 (minimal x0)) /\ (x0 y0)) x1).
Definition term217 := fun y0 : nat -> Prop => exists y1 : nat, (y0 y1) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt y1 (minimal y0)) /\ (y0 y1))).
Definition term52 := fun y0 : nat -> Prop => exists y1 : nat, (y0 y1) /\ (~ (Peano.le (minimal y0) y1)).
Definition term61 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))) /\ ((Peano.lt x1 x0) \/ (Peano.le x0 x1)).
Definition term214 (x0 : nat -> Prop) := (fun y0 : Prop => y0 = (exists y1 : nat, (x0 y1) \/ ((~ (x0 (minimal x0))) \/ ((Peano.lt y1 (minimal x0)) /\ (x0 y1))))) ((exists y0 : nat, x0 y0) \/ (exists y0 : nat, (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0)))).
Definition term279 (x0 : nat) := fun y0 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) y0)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y0) x0)).
Definition term386 (x0 : nat -> Prop) := forall y0 : nat, (fun y1 : nat => (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))) y0.
Definition term350 (x0 : nat -> Prop) := forall y0 : nat, (fun y1 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1))) y0.
Definition term88 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0.
Definition term83 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0.
Definition term363 (x0 : nat -> Prop) := (forall y0 : nat, (fun y1 : nat => ~ (@I (nat -> Prop) x0 y1)) y0) \/ (forall y0 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)))).
Definition term441 (x0 : nat -> Prop) (x1 : nat) := (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0)) x1)) -> @I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0)) x1.
Definition term182 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term237 (x0 : type994) := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => fun y2 : nat => (y1 y2) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0 (x0 y0).
Definition term438 (x0 : nat) (x1 : nat) := @eq Prop ((@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) x0) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le x0) x1)).
Definition term77 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term306 (x0 : type994) (x1 : nat -> Prop) := x1 (x0 x1).
Definition term376 (x0 : nat -> Prop) := fun y0 : nat => (~ (@I (nat -> Prop) x0 y0)) \/ (forall y1 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))).
Definition term269 (x0 : nat) := fun y0 : nat => (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) y0) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y0) x0).
Definition term419 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term203 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0))) x1.
Definition term68 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term149 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (~ ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0)))).
Definition term240 (x0 : type994) := forall y0 : nat -> Prop, (y0 (x0 y0)) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt (x0 y0) (minimal y0)) /\ (y0 (x0 y0)))).
Definition term264 := exists y0 : type994, (forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1))))) /\ (forall y1 : nat -> Prop, (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))).
Definition term129 (x0 : nat -> Prop) := ~ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0)).
Definition term39 (x0 : nat -> Prop) := ~ (forall y0 : nat, (x0 y0) -> Peano.le (minimal x0) y0).
Definition term365 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (@I (nat -> Prop) x0 y0)) x1.
Definition term91 := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term404 := forall y0 : nat -> Prop, forall y1 : nat, forall y2 : nat, ((~ (@I (nat -> Prop) y0 y1)) \/ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0))) /\ ((~ (@I (nat -> Prop) y0 y1)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y2) (@I ((nat -> Prop) -> nat) minimal y0))) \/ (~ (@I (nat -> Prop) y0 y2)))).
Definition term397 := forall y0 : nat -> Prop, forall y1 : nat, forall y2 : nat, (~ (@I (nat -> Prop) y0 y1)) \/ ((@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y2) (@I ((nat -> Prop) -> nat) minimal y0))) \/ (~ (@I (nat -> Prop) y0 y2)))).
Definition term169 := @eq Prop (forall y0 : nat -> Prop, ((exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1)))) /\ ((forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1)))))).
Definition term314 (x0 : type994) (x1 : nat -> Prop) := @I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 x1) (@I ((nat -> Prop) -> nat) minimal x1).
Definition term16 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (minimal x0)) -> ~ (x0 x1).
Definition term194 (x0 : nat -> Prop) := fun y0 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0)).
Definition term124 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (minimal x0)) /\ (~ (~ (x0 x1))).
Definition term3 := ~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1).
Definition term398 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((~ (@I (nat -> Prop) x1 x0)) \/ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1))) /\ ((~ (@I (nat -> Prop) x1 x0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x2) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 x2)))).
Definition term324 (x0 : type994) (x1 : nat -> Prop) := or (x1 (x0 x1)).
Definition term309 (x0 : type994) (x1 : nat -> Prop) := Peano.lt (x0 x1).
Definition term412 (x0 : Prop) := (~ x0) -> x0.
Definition term5 := ((~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False.
Definition term35 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) /\ (~ (Peano.le (minimal x0) x1)).
Definition term333 (x0 : nat -> Prop) (x1 : nat) := Peano.le (@I ((nat -> Prop) -> nat) minimal x0) x1.
Definition term242 := fun y0 : type994 => forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1)))).
Definition term146 (x0 : nat -> Prop) := (~ (exists y0 : nat, x0 y0)) \/ ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))).
Definition term423 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term118 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 y0) x1).
Definition term219 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term135 (x0 : nat -> Prop) := exists y0 : nat, (Peano.lt y0 (minimal x0)) /\ (x0 y0).
Definition term322 (x0 : type994) (x1 : nat -> Prop) := (~ (x1 (minimal x1))) \/ ((Peano.lt (x0 x1) (minimal x1)) /\ (x1 (x0 x1))).
Definition term72 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0)).
Definition term62 (x0 : nat) := fun y0 : nat => ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term103 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0))).
Definition term102 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0)).
Definition term81 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0))).
Definition term80 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0)).
Definition term243 := exists y0 : type994, forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1)))).
Definition term224 := exists y0 : type994, forall y1 : nat -> Prop, (fun y2 : nat -> Prop => fun y3 : nat => (y2 y3) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt y3 (minimal y2)) /\ (y2 y3)))) y1 (y0 y1).
Definition term222 (x0 : type991) := exists y0 : type994, forall y1 : nat -> Prop, x0 y1 (y0 y1).
Definition term382 (x0 : nat) (x1 : nat -> Prop) := (~ (@I (nat -> Prop) x1 x0)) \/ (forall y0 : nat, (fun y1 : nat => (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y1)))) y0).
Definition term389 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (@I (nat -> Prop) x1 x0)) \/ ((fun y0 : nat => (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0)))) x2).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term312 (x0 : type994) (x1 : nat -> Prop) := Peano.lt (@I ((nat -> Prop) -> nat) x0 x1) (@I ((nat -> Prop) -> nat) minimal x1).
Definition term338 (x0 : nat -> Prop) (x1 : nat) := ~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0)) x1).
Definition term12 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False.
Definition term362 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) \/ x1.
Definition term359 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term208 (x0 : nat -> Prop) (x1 : nat) := or (x0 x1).
Definition term380 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (forall y0 : nat, x1 y0).
Definition term216 (x0 : nat -> Prop) := @eq Prop (((exists y0 : nat, x0 y0) \/ (exists y0 : nat, (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0)))) = (exists y0 : nat, (x0 y0) \/ ((~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0))))).
Definition term427 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (@I (nat -> Prop) x0 x1)).
Definition term417 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term15 := (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ~ (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))).
Definition term406 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (@I (nat -> Prop) x0 y0)) \/ (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0))) /\ ((~ (@I (nat -> Prop) x0 y0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1))))) x1.
Definition term313 (x0 : type994) (x1 : nat -> Prop) := @I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 x1).
Definition term202 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ ((fun y1 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y1 (minimal x0)) /\ (x0 y1))) y0).
Definition term141 (x0 : nat -> Prop) := ~ ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))).
Definition term399 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((~ (@I (nat -> Prop) x1 x0)) \/ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1))) /\ ((~ (@I (nat -> Prop) x1 x0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0)))).
Definition term271 := fun y0 : nat => forall y1 : nat, (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) y1) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y1) y0).
Definition term96 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term28 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term54 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term297 (x0 : nat -> Prop) := @I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0).
Definition term147 (x0 : nat -> Prop) := (forall y0 : nat, ~ (x0 y0)) \/ ((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)))).
Definition term89 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term336 (x0 : nat -> Prop) (x1 : nat) := @I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0)) x1.
Definition term150 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ ((~ (x0 (minimal x0))) \/ (exists y0 : nat, (Peano.lt y0 (minimal x0)) /\ (x0 y0))).
Definition term75 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1)).
Definition term22 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term300 (x0 : nat -> Prop) := fun y0 : nat => ~ (@I (nat -> Prop) x0 y0).
Definition term183 (x0 : nat -> Prop) := (~ (x0 (minimal x0))) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (minimal x0)) /\ (x0 y1)) y0).
Definition term292 (x0 : nat) (x1 : nat -> Prop) := or (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) (@I ((nat -> Prop) -> nat) minimal x1))).
Definition term311 (x0 : type994) (x1 : nat -> Prop) := Peano.lt (x0 x1) (minimal x1).
Definition term273 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term349 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1))) y0.
Definition term82 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0.
Definition term346 (x0 : nat -> Prop) := (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ (forall y0 : nat, (fun y1 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1))) y0).
Definition term56 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term50 (x0 : nat -> Prop) := ~ ((fun y0 : nat -> Prop => forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1) x0).
Definition term355 (x0 : nat -> Prop) := fun y0 : nat => (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((fun y1 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1))) y0).
Definition term195 (x0 : nat -> Prop) := exists y0 : nat, (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0)).
Definition term251 := exists y0 : type994, ((fun y1 : type994 => forall y2 : nat -> Prop, (y2 (y1 y2)) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt (y1 y2) (minimal y2)) /\ (y2 (y1 y2))))) y0) /\ (forall y1 : nat -> Prop, (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))).
Definition term9 := ~ (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))).
Definition term33 := fun y0 : nat -> Prop => forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1.
Definition term290 (x0 : nat) (x1 : nat -> Prop) := ~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) (@I ((nat -> Prop) -> nat) minimal x1)).
Definition term254 := exists y0 : type994, (fun y1 : type994 => forall y2 : nat -> Prop, (y2 (y1 y2)) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt (y1 y2) (minimal y2)) /\ (y2 (y1 y2))))) y0.
Definition term26 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term223 := forall y0 : nat -> Prop, exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (y2 y3) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt y3 (minimal y2)) /\ (y2 y3)))) y0 y1.
Definition term221 (x0 : type991) := forall y0 : nat -> Prop, exists y1 : nat, x0 y0 y1.
Definition term241 := fun y0 : type994 => forall y1 : nat -> Prop, (fun y2 : nat -> Prop => fun y3 : nat => (y2 y3) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt y3 (minimal y2)) /\ (y2 y3)))) y1 (y0 y1).
Definition term433 (x0 : nat -> Prop) (x1 : nat) := (@I (nat -> Prop) x0 x1) /\ (@I (nat -> Prop) x0 x1).
Definition term86 (x0 : nat) := and (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))).
Definition term139 (x0 : nat -> Prop) := (~ (x0 (minimal x0))) \/ (~ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))).
Definition term157 (x0 : type993) (x1 : type993) := forall y0 : nat -> Prop, (x0 y0) /\ (x1 y0).
Definition term233 := @eq Prop (forall y0 : nat -> Prop, exists y1 : nat, (y0 y1) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt y1 (minimal y0)) /\ (y0 y1)))).
Definition term232 := @eq Prop (forall y0 : nat -> Prop, exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (y2 y3) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt y3 (minimal y2)) /\ (y2 y3)))) y0 y1).
Definition term370 (x0 : nat -> Prop) := @eq Prop ((forall y0 : nat, ~ (@I (nat -> Prop) x0 y0)) \/ (forall y0 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))))).
Definition term369 (x0 : nat -> Prop) := @eq Prop ((forall y0 : nat, (fun y1 : nat => ~ (@I (nat -> Prop) x0 y1)) y0) \/ (forall y0 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))))).
Definition term317 (x0 : type994) (x1 : nat -> Prop) := and (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 x1)) (@I ((nat -> Prop) -> nat) minimal x1)).
Definition term180 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term176 := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))) y0.
Definition term171 := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (exists y2 : nat, y1 y2) \/ ((~ (y1 (minimal y1))) \/ (exists y2 : nat, (Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0.
Definition term374 (x0 : nat) (x1 : nat -> Prop) := (~ (@I (nat -> Prop) x1 x0)) \/ (forall y0 : nat, (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0)))).
Definition term204 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y1 (minimal x0)) /\ (x0 y1))) y0.
Definition term142 (x0 : nat -> Prop) := x0 (minimal x0).
Definition term393 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (@I (nat -> Prop) x1 x0)) \/ ((@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0)))).
Definition term422 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term187 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 (minimal x0)) /\ (x0 y1)) y0.
Definition term402 (x0 : nat -> Prop) := forall y0 : nat, forall y1 : nat, ((~ (@I (nat -> Prop) x0 y0)) \/ (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0))) /\ ((~ (@I (nat -> Prop) x0 y0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))).
Definition term395 (x0 : nat -> Prop) := forall y0 : nat, forall y1 : nat, (~ (@I (nat -> Prop) x0 y0)) \/ ((@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))).
Definition term282 := forall y0 : nat, forall y1 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) y1)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y1) y0)).
Definition term272 := forall y0 : nat, forall y1 : nat, (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) y1) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y1) y0).
Definition term111 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term106 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0)).
Definition term65 := forall y0 : nat, forall y1 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ ((Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term29 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term131 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 (minimal x0)) -> ~ (x0 y0)) x1.
Definition term179 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term345 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 /\ (x1 y0).
Definition term371 (x0 : nat -> Prop) (x1 : nat) := or ((fun y0 : nat => ~ (@I (nat -> Prop) x0 y0)) x1).
Definition term255 := and (exists y0 : type994, (fun y1 : type994 => forall y2 : nat -> Prop, (y2 (y1 y2)) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt (y1 y2) (minimal y2)) /\ (y2 (y1 y2))))) y0).
Definition term100 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0).
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term413 (x0 : nat) (x1 : nat -> Prop) := (~ (@I (nat -> Prop) x1 x0)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) (@I ((nat -> Prop) -> nat) minimal x1))).
Definition term361 (x0 : nat -> Prop) (x1 : Prop) := (forall y0 : nat, x0 y0) \/ x1.
Definition term431 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((@I (nat -> Prop) x1 x0) /\ (@I (nat -> Prop) x1 x2)).
Definition term175 := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))) y0.
Definition term170 := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => (exists y2 : nat, y1 y2) \/ ((~ (y1 (minimal y1))) \/ (exists y2 : nat, (Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0.
Definition term148 (x0 : nat -> Prop) := or (exists y0 : nat, x0 y0).
Definition term392 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (@I (nat -> Prop) x1 x0)) \/ ((@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0)))).
Definition term113 (x0 : nat -> Prop) := ~ (ex x0).
Definition term27 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term289 (x0 : nat) (x1 : nat -> Prop) := ~ (Peano.lt x0 (minimal x1)).
Definition term155 := fun y0 : nat -> Prop => ((exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1)))) /\ ((forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))).
Definition term184 (x0 : nat -> Prop) := exists y0 : nat, (~ (x0 (minimal x0))) \/ ((fun y1 : nat => (Peano.lt y1 (minimal x0)) /\ (x0 y1)) y0).
Definition term57 (x0 : nat) (x1 : nat) := (~ (~ (Peano.lt x1 x0))) \/ (Peano.le x0 x1).
Definition term308 (x0 : type994) (x1 : nat -> Prop) := @I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) x0 x1).
Definition term117 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term59 (x0 : nat) (x1 : nat) := and ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term6 := (((~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False.
Definition term325 (x0 : type994) (x1 : nat -> Prop) := or (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) x0 x1)).
Definition term258 (x0 : type994) := and ((fun y0 : type994 => forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1))))) x0).
Definition term236 (x0 : type994) (x1 : nat -> Prop) := (x1 (x0 x1)) \/ ((~ (x1 (minimal x1))) \/ ((Peano.lt (x0 x1) (minimal x1)) /\ (x1 (x0 x1)))).
Definition term186 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 (minimal x0)) /\ (x0 y0)) x1.
Definition term249 (x0 : type252) (x1 : Prop) := exists y0 : type994, (x0 y0) /\ x1.
Definition term304 := fun y0 : nat -> Prop => (forall y1 : nat, ~ (@I (nat -> Prop) y0 y1)) \/ ((@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0)) /\ (forall y1 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal y0))) \/ (~ (@I (nat -> Prop) y0 y1)))).
Definition term229 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat -> Prop => fun y2 : nat => (y1 y2) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt y2 (minimal y1)) /\ (y1 y2)))) x0 y0.
Definition term167 := fun y0 : nat -> Prop => ((fun y1 : nat -> Prop => (exists y2 : nat, y1 y2) \/ ((~ (y1 (minimal y1))) \/ (exists y2 : nat, (Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0) /\ ((fun y1 : nat -> Prop => (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))) y0).
Definition term123 (x0 : nat) (x1 : nat -> Prop) := and (Peano.lt x0 (minimal x1)).
Definition term275 (x0 : nat) (x1 : nat) := ~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) x1).
Definition term274 (x0 : nat) (x1 : nat) := ~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le x0) x1).
Definition term8 := (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False.
Definition term45 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (~ (Peano.le (minimal x0) y0)).
Definition term114 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term410 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (@I (nat -> Prop) x1 x0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x2) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 x2))).
Definition term277 (x0 : nat) (x1 : nat) := or (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) x1)).
Definition term226 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => fun y1 : nat => (y0 y1) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt y1 (minimal y0)) /\ (y0 y1)))) x0.
Definition term416 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((~ (@I (nat -> Prop) x2 x0)) \/ ((~ (@I (nat -> Prop) x2 x1)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) (@I ((nat -> Prop) -> nat) minimal x2))))).
Definition term415 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (@I (nat -> Prop) x1 x0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x2) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 x2)))).
Definition term334 (x0 : nat -> Prop) := @I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0).
Definition term2 := (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> False.
Definition term301 (x0 : nat -> Prop) := forall y0 : nat, ~ (@I (nat -> Prop) x0 y0).
Definition term168 := @eq Prop (forall y0 : nat -> Prop, ((fun y1 : nat -> Prop => (exists y2 : nat, y1 y2) \/ ((~ (y1 (minimal y1))) \/ (exists y2 : nat, (Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0) /\ ((fun y1 : nat -> Prop => (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))) y0)).
Definition term260 (x0 : type994) := ((fun y0 : type994 => forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1))))) x0) /\ (forall y0 : nat -> Prop, (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))).
Definition term291 (x0 : nat) (x1 : nat -> Prop) := or (~ (Peano.lt x0 (minimal x1))).
Definition term302 (x0 : nat -> Prop) := or (forall y0 : nat, ~ (@I (nat -> Prop) x0 y0)).
Definition term145 (x0 : nat -> Prop) := or (forall y0 : nat, ~ (x0 y0)).
Definition term375 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => ~ (@I (nat -> Prop) x0 y1)) y0) \/ (forall y1 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))).
Definition term343 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 /\ (x1 y0).
Definition term41 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 y0) -> Peano.le (minimal x0) y0) x1.
Definition term30 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> Peano.le (minimal x0) x1.
Definition term78 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1) /\ ((fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1).
Definition term69 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term231 := fun y0 : nat -> Prop => exists y1 : nat, (fun y2 : nat -> Prop => fun y3 : nat => (y2 y3) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt y3 (minimal y2)) /\ (y2 y3)))) y0 y1.
Definition term228 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (x0 y0) \/ ((~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0)))) x1.
Definition term344 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (forall y0 : nat, x1 y0).
Definition term122 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term267 (x0 : nat) (x1 : nat) := or (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) x1).
Definition term152 (x0 : nat -> Prop) := and ((exists y0 : nat, x0 y0) \/ ((~ (x0 (minimal x0))) \/ (exists y0 : nat, (Peano.lt y0 (minimal x0)) /\ (x0 y0)))).
Definition term360 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term420 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ ((~ (@I (nat -> Prop) x2 x0)) \/ (~ (@I (nat -> Prop) x2 x1)))) -> ~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) (@I ((nat -> Prop) -> nat) minimal x2)).
Definition term205 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y1 (minimal x0)) /\ (x0 y1))) y0.
Definition term188 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (minimal x0)) /\ (x0 y1)) y0.
Definition term7 := (((~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False) -> ((~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False.
Definition term227 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat -> Prop => fun y1 : nat => (y0 y1) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt y1 (minimal y0)) /\ (y0 y1)))) x0 x1.
Definition term296 (x0 : nat -> Prop) := x0 (@I ((nat -> Prop) -> nat) minimal x0).
Definition term364 (x0 : nat -> Prop) := forall y0 : nat, ((fun y1 : nat => ~ (@I (nat -> Prop) x0 y1)) y0) \/ (forall y1 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))).
Definition term252 (x0 : type994) := (fun y0 : type994 => forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1))))) x0.
Definition term428 (x0 : nat -> Prop) (x1 : nat) := and (~ (~ (@I (nat -> Prop) x0 x1))).
Definition term294 (x0 : nat -> Prop) := fun y0 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)).
Definition term164 (x0 : nat -> Prop) := and ((fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1)))) x0).
Definition term120 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 y1) y0).
Definition term411 (x0 : nat -> Prop) (x1 : nat) := (~ (@I (nat -> Prop) x0 x1)) -> @I (nat -> Prop) x0 x1.
Definition term201 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y1 (minimal x0)) /\ (x0 y1))) y0).
Definition term90 (x0 : nat) := (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ (forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term337 (x0 : nat -> Prop) (x1 : nat) := ~ (Peano.le (minimal x0) x1).
Definition term210 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) \/ ((~ (x0 (minimal x0))) \/ ((Peano.lt x1 (minimal x0)) /\ (x0 x1))).
Definition term321 (x0 : nat -> Prop) := or (~ (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0))).
Definition term283 := and (forall y0 : nat, forall y1 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) y1)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y1) y0))).
Definition term108 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))).
Definition term235 (x0 : type994) (x1 : nat -> Prop) := (fun y0 : nat => (x1 y0) \/ ((~ (x1 (minimal x1))) \/ ((Peano.lt y0 (minimal x1)) /\ (x1 y0)))) (x0 x1).
Definition term288 (x0 : nat) (x1 : nat -> Prop) := @I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) (@I ((nat -> Prop) -> nat) minimal x1).
Definition term239 (x0 : type994) := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => fun y2 : nat => (y1 y2) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0 (x0 y0).
Definition term25 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term1 := forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1.
Definition term248 (x0 : type252) (x1 : Prop) := (exists y0 : type994, x0 y0) /\ x1.
Definition term265 (x0 : nat) (x1 : nat) := @I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le x0) x1.
Definition term165 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))) x0.
Definition term163 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1)))) x0.
Definition term116 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 y1) y0).
Definition term293 (x0 : nat -> Prop) (x1 : nat) := (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 x1)).
Definition term109 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term104 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0.
Definition term408 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) y1) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y1) y0)) x0.
Definition term99 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term97 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0.
Definition term315 (x0 : type994) (x1 : nat -> Prop) := @I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 x1)) (@I ((nat -> Prop) -> nat) minimal x1).
Definition term340 (x0 : nat -> Prop) (x1 : nat) := and (@I (nat -> Prop) x0 x1).
Definition term440 (x0 : nat -> Prop) (x1 : nat) := (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) (@I ((nat -> Prop) -> nat) minimal x0))) -> @I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0)) x1.
Definition term10 := forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1))).
Definition term310 (x0 : type994) (x1 : nat -> Prop) := Peano.lt (@I ((nat -> Prop) -> nat) x0 x1).
Definition term373 (x0 : nat) (x1 : nat -> Prop) := ((fun y0 : nat => ~ (@I (nat -> Prop) x1 y0)) x0) \/ (forall y0 : nat, (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0)))).
Definition term36 (x0 : nat -> Prop) (x1 : nat) := Peano.le (minimal x0) x1.
Definition term429 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (@I (nat -> Prop) x1 x0) /\ (@I (nat -> Prop) x1 x2).
Definition term245 := (exists y0 : type994, forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1))))) /\ (forall y0 : nat -> Prop, (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))).
Definition term17 (x0 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 (minimal x0)) -> ~ (x0 y0).
Definition term354 (x0 : nat -> Prop) (x1 : nat) := (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 x1))).
Definition term384 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)))) x1.
Definition term32 (x0 : nat -> Prop) := forall y0 : nat, (x0 y0) -> Peano.le (minimal x0) y0.
Definition term295 (x0 : nat -> Prop) := forall y0 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)).
Definition term280 (x0 : nat) := forall y0 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) y0)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y0) x0)).
Definition term84 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0)).
Definition term153 (x0 : nat -> Prop) := ((exists y0 : nat, x0 y0) \/ (~ ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))))) /\ ((~ (exists y0 : nat, x0 y0)) \/ ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0)))).
Definition term320 (x0 : nat -> Prop) := ~ (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)).
Definition term424 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((~ (@I (nat -> Prop) x1 x0)) \/ (~ (@I (nat -> Prop) x1 x2))).
Definition term160 := (forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (exists y2 : nat, y1 y2) \/ ((~ (y1 (minimal y1))) \/ (exists y2 : nat, (Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0) /\ (forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))) y0).
Definition term130 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt y1 (minimal x0)) -> ~ (x0 y1)) y0).
Definition term40 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (x0 y1) -> Peano.le (minimal x0) y1) y0).
Definition term307 (x0 : type994) (x1 : nat -> Prop) := x1 (@I ((nat -> Prop) -> nat) x0 x1).
Definition term143 (x0 : nat -> Prop) := (x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0))).
Definition term20 (x0 : nat -> Prop) := (x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0)).
Definition term381 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 \/ (x1 y0).
Definition term353 (x0 : nat -> Prop) (x1 : nat) := (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((fun y0 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))) x1).
Definition term305 := forall y0 : nat -> Prop, (forall y1 : nat, ~ (@I (nat -> Prop) y0 y1)) \/ ((@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0)) /\ (forall y1 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal y0))) \/ (~ (@I (nat -> Prop) y0 y1)))).
Definition term177 := forall y0 : nat -> Prop, (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1)))).
Definition term172 := forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1))).
Definition term87 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0.
Definition term13 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> ~ (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))).
Definition term212 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) \/ ((~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0))).
Definition term385 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))) y0.
Definition term190 (x0 : nat -> Prop) := @eq Prop ((~ (x0 (minimal x0))) \/ (exists y0 : nat, (Peano.lt y0 (minimal x0)) /\ (x0 y0))).
Definition term189 (x0 : nat -> Prop) := @eq Prop ((~ (x0 (minimal x0))) \/ (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 (minimal x0)) /\ (x0 y1)) y0)).
Definition term328 (x0 : type994) := forall y0 : nat -> Prop, (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) x0 y0)) \/ ((~ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0))) \/ ((@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 y0)) (@I ((nat -> Prop) -> nat) minimal y0)) /\ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) x0 y0)))).
Definition term107 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0).
Definition term85 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0).
Definition term432 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((@I (nat -> Prop) x2 x0) /\ (@I (nat -> Prop) x2 x1)) -> ~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) (@I ((nat -> Prop) -> nat) minimal x2)).
Definition term98 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0).
Definition term357 (x0 : nat -> Prop) := forall y0 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))).
Definition term60 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))) /\ ((~ (~ (Peano.lt x1 x0))) \/ (Peano.le x0 x1)).
Definition term390 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (@I (nat -> Prop) x1 x0)) \/ ((@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x2) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 x2)))).
Definition term211 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) \/ ((fun y1 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y1 (minimal x0)) /\ (x0 y1))) y0).
Definition term366 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => ~ (@I (nat -> Prop) x0 y1)) y0.
Definition term196 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0))).
Definition term225 := fun y0 : nat -> Prop => fun y1 : nat => (y0 y1) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt y1 (minimal y0)) /\ (y0 y1))).
Definition term250 := (exists y0 : type994, (fun y1 : type994 => forall y2 : nat -> Prop, (y2 (y1 y2)) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt (y1 y2) (minimal y2)) /\ (y2 (y1 y2))))) y0) /\ (forall y0 : nat -> Prop, (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))).
Definition term154 (x0 : nat -> Prop) := ((exists y0 : nat, x0 y0) \/ ((~ (x0 (minimal x0))) \/ (exists y0 : nat, (Peano.lt y0 (minimal x0)) /\ (x0 y0)))) /\ ((forall y0 : nat, ~ (x0 y0)) \/ ((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0))))).
Definition term335 (x0 : nat -> Prop) (x1 : nat) := @I (nat -> nat -> Prop) Peano.le (@I ((nat -> Prop) -> nat) minimal x0) x1.
Definition term55 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.lt x0 x1))).
Definition term281 := fun y0 : nat => forall y1 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) y1)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y1) y0)).
Definition term95 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0)).
Definition term173 := and (forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (exists y2 : nat, y1 y2) \/ ((~ (y1 (minimal y1))) \/ (exists y2 : nat, (Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term115 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term92 := forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term49 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1) x0.
Definition term285 (x0 : nat -> Prop) (x1 : nat) := ~ (@I (nat -> Prop) x0 x1).
Definition term162 := fun y0 : nat -> Prop => (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1)))).
Definition term339 (x0 : nat -> Prop) (x1 : nat) := and (x0 x1).
Definition term200 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term319 (x0 : type994) (x1 : nat -> Prop) := (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 x1)) (@I ((nat -> Prop) -> nat) minimal x1)) /\ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) x0 x1)).
Definition term238 (x0 : type994) := fun y0 : nat -> Prop => (y0 (x0 y0)) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt (x0 y0) (minimal y0)) /\ (y0 (x0 y0)))).
Definition term18 (x0 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0).
Definition term47 (x0 : type993) := exists y0 : nat -> Prop, ~ (x0 y0).
Definition term298 (x0 : nat -> Prop) := and (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)).
Definition term76 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1).
Definition term133 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt y1 (minimal x0)) -> ~ (x0 y1)) y0).
Definition term43 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (x0 y1) -> Peano.le (minimal x0) y1) y0).
Definition term23 (x0 : nat -> Prop) := @eq Prop (exists y0 : nat, x0 y0).
Definition term435 (x0 : nat) (x1 : nat -> Prop) := (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) (@I ((nat -> Prop) -> nat) minimal x1)) -> ~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) (@I ((nat -> Prop) -> nat) minimal x1)).
Definition term132 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => (Peano.lt y0 (minimal x0)) -> ~ (x0 y0)) x1).
Definition term42 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => (x0 y0) -> Peano.le (minimal x0) y0) x1).
Definition term257 := @eq Prop ((exists y0 : type994, forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1))))) /\ (forall y0 : nat -> Prop, (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1)))))).
Definition term256 := @eq Prop ((exists y0 : type994, (fun y1 : type994 => forall y2 : nat -> Prop, (y2 (y1 y2)) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt (y1 y2) (minimal y2)) /\ (y2 (y1 y2))))) y0) /\ (forall y0 : nat -> Prop, (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1)))))).
Definition term418 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x2) (@I ((nat -> Prop) -> nat) minimal x1))) \/ ((~ (@I (nat -> Prop) x1 x0)) \/ (~ (@I (nat -> Prop) x1 x2))).
Definition term128 (x0 : nat -> Prop) (x1 : nat) := (~ (Peano.lt x1 (minimal x0))) \/ (~ (x0 x1)).
Definition term134 (x0 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 (minimal x0)) /\ (x0 y0).
Definition term144 (x0 : nat -> Prop) := or (~ (exists y0 : nat, x0 y0)).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term434 (x0 : nat) (x1 : nat -> Prop) := ((@I (nat -> Prop) x1 x0) /\ (@I (nat -> Prop) x1 x0)) -> ~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) (@I ((nat -> Prop) -> nat) minimal x1)).
Definition term329 (x0 : type994) := and (forall y0 : nat -> Prop, (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) x0 y0)) \/ ((~ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0))) \/ ((@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 y0)) (@I ((nat -> Prop) -> nat) minimal y0)) /\ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) x0 y0))))).
Definition term259 (x0 : type994) := and (forall y0 : nat -> Prop, (y0 (x0 y0)) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt (x0 y0) (minimal y0)) /\ (y0 (x0 y0))))).
Definition term174 := and (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1)))).
Definition term110 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term105 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0.
Definition term220 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term11 := imp (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term330 (x0 : type994) := (forall y0 : nat -> Prop, (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) x0 y0)) \/ ((~ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0))) \/ ((@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 y0)) (@I ((nat -> Prop) -> nat) minimal y0)) /\ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) x0 y0))))) /\ (forall y0 : nat -> Prop, (forall y1 : nat, ~ (@I (nat -> Prop) y0 y1)) \/ ((@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0)) /\ (forall y1 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal y0))) \/ (~ (@I (nat -> Prop) y0 y1))))).
Definition term261 (x0 : type994) := (forall y0 : nat -> Prop, (y0 (x0 y0)) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt (x0 y0) (minimal y0)) /\ (y0 (x0 y0))))) /\ (forall y0 : nat -> Prop, (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))).
Definition term178 := (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1)))) /\ (forall y0 : nat -> Prop, (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))).
Definition term323 (x0 : type994) (x1 : nat -> Prop) := (~ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1))) \/ ((@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 x1)) (@I ((nat -> Prop) -> nat) minimal x1)) /\ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) x0 x1))).
Definition term347 (x0 : nat -> Prop) := forall y0 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((fun y1 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1))) y0).
Definition term198 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term421 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (@I (nat -> Prop) x1 x0)) \/ (~ (@I (nat -> Prop) x1 x2)).
Definition term166 (x0 : nat -> Prop) := ((fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1)))) x0) /\ ((fun y0 : nat -> Prop => (forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))) x0).
Definition term159 := forall y0 : nat -> Prop, ((fun y1 : nat -> Prop => (exists y2 : nat, y1 y2) \/ ((~ (y1 (minimal y1))) \/ (exists y2 : nat, (Peano.lt y2 (minimal y1)) /\ (y1 y2)))) y0) /\ ((fun y1 : nat -> Prop => (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))) y0).
Definition term4 := (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> (forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) -> False.
Definition term38 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term352 (x0 : nat -> Prop) := @eq Prop ((@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ (forall y0 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)))).
Definition term351 (x0 : nat -> Prop) := @eq Prop ((@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ (forall y0 : nat, (fun y1 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1))) y0)).
Definition term181 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term266 (x0 : nat) (x1 : nat) := @I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) x1.
Definition term218 := forall y0 : nat -> Prop, exists y1 : nat, (y0 y1) \/ ((~ (y0 (minimal y0))) \/ ((Peano.lt y1 (minimal y0)) /\ (y0 y1))).
Definition term209 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) \/ ((fun y0 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0))) x1).
Definition term125 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (minimal x0)) /\ (x0 x1).
Definition term158 (x0 : type993) (x1 : type993) := (forall y0 : nat -> Prop, x0 y0) /\ (forall y0 : nat -> Prop, x1 y0).
Definition term414 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ (@I (nat -> Prop) x2 x0)) \/ ((~ (@I (nat -> Prop) x2 x1)) \/ (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x1) (@I ((nat -> Prop) -> nat) minimal x2)))).
Definition term348 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))) x1.
Definition term74 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1.
Definition term401 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, ((~ (@I (nat -> Prop) x0 y0)) \/ (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0))) /\ ((~ (@I (nat -> Prop) x0 y0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))).
Definition term394 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (~ (@I (nat -> Prop) x0 y0)) \/ ((@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))).
Definition term64 := fun y0 : nat => forall y1 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ ((Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term409 (x0 : nat) (x1 : nat) := (fun y0 : nat => (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt x0) y0) \/ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.le y0) x0)) x1.
Definition term263 := fun y0 : type994 => (forall y1 : nat -> Prop, (y1 (y0 y1)) \/ ((~ (y1 (minimal y1))) \/ ((Peano.lt (y0 y1) (minimal y1)) /\ (y1 (y0 y1))))) /\ (forall y1 : nat -> Prop, (forall y2 : nat, ~ (y1 y2)) \/ ((y1 (minimal y1)) /\ (forall y2 : nat, (~ (Peano.lt y2 (minimal y1))) \/ (~ (y1 y2))))).
Definition term199 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term327 (x0 : type994) := fun y0 : nat -> Prop => (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) x0 y0)) \/ ((~ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) minimal y0))) \/ ((@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt (@I ((nat -> Prop) -> nat) x0 y0)) (@I ((nat -> Prop) -> nat) minimal y0)) /\ (@I (nat -> Prop) y0 (@I ((nat -> Prop) -> nat) x0 y0)))).
Definition term156 := forall y0 : nat -> Prop, ((exists y1 : nat, y0 y1) \/ ((~ (y0 (minimal y0))) \/ (exists y1 : nat, (Peano.lt y1 (minimal y0)) /\ (y0 y1)))) /\ ((forall y1 : nat, ~ (y0 y1)) \/ ((y0 (minimal y0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal y0))) \/ (~ (y0 y1))))).
Definition term400 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ((~ (@I (nat -> Prop) x1 x0)) \/ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1))) /\ ((~ (@I (nat -> Prop) x1 x0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0)))).
Definition term44 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) /\ (~ (Peano.le (minimal x0) y0)).
Definition term358 (x0 : nat -> Prop) := (forall y0 : nat, ~ (@I (nat -> Prop) x0 y0)) \/ (forall y0 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)))).
Definition term14 := imp (~ (forall y0 : nat -> Prop, forall y1 : nat, (y0 y1) -> Peano.le (minimal y0) y1)).
Definition term436 (x0 : Prop) := x0 -> ~ x0.
Definition term140 (x0 : nat -> Prop) := (~ (x0 (minimal x0))) \/ (exists y0 : nat, (Peano.lt y0 (minimal x0)) /\ (x0 y0)).
Definition term383 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (@I (nat -> Prop) x1 x0)) \/ ((fun y1 : nat => (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y1)))) y0).
Definition term121 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term303 (x0 : nat -> Prop) := (forall y0 : nat, ~ (@I (nat -> Prop) x0 y0)) \/ ((@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ (forall y0 : nat, (~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)))).
Definition term253 := fun y0 : type994 => (fun y1 : type994 => forall y2 : nat -> Prop, (y2 (y1 y2)) \/ ((~ (y2 (minimal y2))) \/ ((Peano.lt (y1 y2) (minimal y2)) /\ (y2 (y1 y2))))) y0.
Definition term377 (x0 : nat -> Prop) := forall y0 : nat, (~ (@I (nat -> Prop) x0 y0)) \/ (forall y1 : nat, (@I (nat -> Prop) x0 (@I ((nat -> Prop) -> nat) minimal x0)) /\ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y1) (@I ((nat -> Prop) -> nat) minimal x0))) \/ (~ (@I (nat -> Prop) x0 y1)))).
Definition term58 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ (Peano.le x0 x1).
Definition term287 (x0 : nat) (x1 : nat -> Prop) := @I (nat -> nat -> Prop) Peano.lt x0 (@I ((nat -> Prop) -> nat) minimal x1).
Definition term342 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (forall y0 : a0, x1 y0).
Definition term407 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => ((~ (@I (nat -> Prop) x1 x0)) \/ (@I (nat -> Prop) x1 (@I ((nat -> Prop) -> nat) minimal x1))) /\ ((~ (@I (nat -> Prop) x1 x0)) \/ ((~ (@I (nat -> Prop) (@I (nat -> nat -> Prop) Peano.lt y0) (@I ((nat -> Prop) -> nat) minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0))))) x2.
Definition term137 (x0 : nat -> Prop) := forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)).
Definition term207 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, x0 y0) \/ (exists y0 : nat, (~ (x0 (minimal x0))) \/ ((Peano.lt y0 (minimal x0)) /\ (x0 y0)))).
Definition term206 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, x0 y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (x0 (minimal x0))) \/ ((Peano.lt y1 (minimal x0)) /\ (x0 y1))) y0)).
