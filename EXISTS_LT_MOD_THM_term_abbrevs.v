Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term488 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term542 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0))).
Definition term522 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term541 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term433 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term376 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) \/ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) \/ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0).
Definition term320 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) \/ (y2 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) \/ (~ (y2 = (NUMERAL 0)))) y0).
Definition term104 (x0 : type993) := ~ (all x0).
Definition term95 (x0 : nat -> Prop) := ~ (all x0).
Definition term466 := (~ False) -> False.
Definition term389 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)).
Definition term482 (x0 : nat) (x1 : nat) := (~ ((Nat.modulo x1 x0) = x1)) -> (Nat.modulo x1 x0) = x1.
Definition term513 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term171 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0)) x2).
Definition term495 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term109 := fun y0 : nat -> Prop => ~ ((fun y1 : nat -> Prop => forall y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) = ((~ (y2 = (NUMERAL 0))) /\ (exists y3 : nat, y1 (Nat.modulo y3 y2)))) y0).
Definition term201 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1))) x2.
Definition term121 (x0 : nat -> Prop) (x1 : nat) := or ((fun y0 : nat => (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0))))) x1).
Definition term425 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term403 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term368 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) \/ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) \/ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0).
Definition term346 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Nat.modulo x0 y1) = x0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0).
Definition term312 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) \/ (y2 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) \/ (~ (y2 = (NUMERAL 0)))) y0).
Definition term290 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) \/ (y1 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term158 := exists y0 : nat -> Prop, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))).
Definition term153 := exists y0 : nat -> Prop, exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1)))).
Definition term111 := exists y0 : nat -> Prop, exists y1 : nat, ((exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) \/ ((forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))).
Definition term477 (x0 : Prop) := ~ (~ x0).
Definition term175 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt y1 x1) /\ (x0 y1)) y0) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1)))).
Definition term29 := (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ~ ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term531 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x0 (Nat.modulo x1 x2))) -> x0 (Nat.modulo x1 x2).
Definition term106 := exists y0 : nat -> Prop, ~ ((fun y1 : nat -> Prop => forall y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) = ((~ (y2 = (NUMERAL 0))) /\ (exists y3 : nat, y1 (Nat.modulo y3 y2)))) y0).
Definition term265 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1))))) x2) \/ ((fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1)))) x2).
Definition term523 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (x1 x2))).
Definition term227 (x0 : nat -> Prop) := or ((fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) x0).
Definition term145 (x0 : nat -> Prop) := or ((fun y0 : nat -> Prop => exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) x0).
Definition term411 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term354 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Nat.modulo x0 y1) = x0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0).
Definition term298 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) \/ (y1 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term89 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x0 (Nat.modulo y0 x1)))).
Definition term456 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt y0 x0)) \/ (~ (x1 y0))) x2.
Definition term393 (x0 : nat) (x1 : nat) := (Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1))).
Definition term24 := (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ~ ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term270 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) \/ ((forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0)))).
Definition term211 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0))).
Definition term178 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0)))).
Definition term529 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = (Nat.modulo x2 x0)) /\ (x1 x2).
Definition term83 (x0 : nat) (x1 : nat -> Prop) := and (~ (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0))).
Definition term246 (x0 : nat -> Prop) (x1 : nat) := or (exists y0 : nat, ((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1))))).
Definition term131 (x0 : nat -> Prop) := or (exists y0 : nat, (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0))))).
Definition term516 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x0 x1)) \/ (~ (x1 = x2)).
Definition term500 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term248 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, ((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1))))) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1)))).
Definition term135 (x0 : nat -> Prop) := (exists y0 : nat, (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0))))) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0)))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term359 (x0 : nat) := forall y0 : nat, ((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0))).
Definition term76 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ~ (x0 (Nat.modulo y0 x1)).
Definition term294 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0))) x1.
Definition term134 (x0 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0))).
Definition term129 (x0 : nat -> Prop) := exists y0 : nat, (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0)))).
Definition term280 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.modulo x0 x1) x1) \/ (~ (~ (x1 = (NUMERAL 0))))) /\ ((~ (Peano.lt (Nat.modulo x0 x1) x1)) \/ (~ (x1 = (NUMERAL 0)))).
Definition term17 := and (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False).
Definition term184 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term46 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := x0 (Nat.modulo x1 x2).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term426 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term404 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term369 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) \/ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) \/ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0).
Definition term347 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => ((Nat.modulo x0 y1) = x0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0).
Definition term313 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) \/ (y2 = (NUMERAL 0))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) \/ (~ (y2 = (NUMERAL 0)))) y0).
Definition term291 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) \/ (y1 = (NUMERAL 0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0).
Definition term444 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term387 := (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term331 := (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))).
Definition term505 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term446 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = x0) \/ (~ (x1 = (NUMERAL 0)))) /\ (((Nat.modulo x0 x1) = x0) \/ (~ (Peano.lt x0 x1))).
Definition term470 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) -> (x1 x0) \/ (~ (x1 x2)).
Definition term274 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) \/ (~ (x1 = (NUMERAL 0))).
Definition term406 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term538 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term457 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) \/ (~ (Peano.lt x0 x1)).
Definition term511 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.modulo x0 x1)).
Definition term143 := fun y0 : nat -> Prop => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))).
Definition term142 := fun y0 : nat -> Prop => exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1)))).
Definition term110 := fun y0 : nat -> Prop => exists y1 : nat, ((exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) \/ ((forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))).
Definition term275 (x0 : nat) (x1 : nat) := or (Peano.lt (Nat.modulo x0 x1) x1).
Definition term420 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0.
Definition term415 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term363 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0.
Definition term358 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.modulo x0 y1) = x0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term307 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term302 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) \/ (y1 = (NUMERAL 0))) y0.
Definition term535 (x0 : nat -> Prop) (x1 : nat) := imp (x0 x1).
Definition term197 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1)).
Definition term64 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0)) x2.
Definition term269 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1))))) \/ ((forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1)))).
Definition term103 (x0 : nat -> Prop) := exists y0 : nat, ((exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0))))) \/ ((forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0)))).
Definition term281 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0))) /\ ((~ (Peano.lt (Nat.modulo x0 x1) x1)) \/ (~ (x1 = (NUMERAL 0)))).
Definition term177 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1)))).
Definition term173 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((fun y0 : nat => (Peano.lt y0 x2) /\ (x1 y0)) x0) /\ ((x2 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x1 (Nat.modulo y0 x2)))).
Definition term475 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term288 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term503 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term182 := or (exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))).
Definition term155 := or (exists y0 : nat -> Prop, exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))).
Definition term97 (x0 : nat -> Prop) := ~ (forall y0 : nat, (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) = ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0)))).
Definition term423 := fun y0 : nat => (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term366 := fun y0 : nat => (forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term310 := fun y0 : nat => (forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) /\ (forall y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))).
Definition term99 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) = ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0)))) x1.
Definition term303 (x0 : nat) := forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0)).
Definition term454 (x0 : nat) (x1 : nat) := (fun y0 : nat => (((Nat.modulo x0 y0) = x0) \/ (~ (y0 = (NUMERAL 0)))) /\ (((Nat.modulo x0 y0) = x0) \/ (~ (Peano.lt x0 y0)))) x1.
Definition term273 := exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, (((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) \/ ((forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1)))).
Definition term214 := exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1))).
Definition term181 := exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1)))).
Definition term183 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term198 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0))) /\ (exists y0 : nat, (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1))).
Definition term18 := and (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term3 := ~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))).
Definition term348 (x0 : nat) := fun y0 : nat => ((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0))).
Definition term233 := exists y0 : nat -> Prop, (exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) \/ (exists y1 : nat, exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1)))).
Definition term137 := exists y0 : nat -> Prop, (exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))).
Definition term464 (x0 : Prop) := (~ x0) -> x0.
Definition term504 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term150 := @eq Prop (exists y0 : nat -> Prop, (exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))).
Definition term536 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x1) -> ~ (Peano.lt x1 x2).
Definition term93 (x0 : nat -> Prop) (x1 : nat) := ((exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x0 (Nat.modulo y0 x1))))) \/ ((forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0))) /\ ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1)))).
Definition term496 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term15 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term207 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x0 y0))) /\ ((~ (x2 = (NUMERAL 0))) /\ (x0 (Nat.modulo x1 x2))).
Definition term264 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := or (((Peano.lt x0 x2) /\ (x1 x0)) /\ ((x2 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x1 (Nat.modulo y0 x2))))).
Definition term545 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term32 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term498 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term174 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((Peano.lt x0 x2) /\ (x1 x0)) /\ ((x2 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x1 (Nat.modulo y0 x2)))).
Definition term80 (x0 : nat -> Prop) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ (~ (exists y0 : nat, x0 (Nat.modulo y0 x1))).
Definition term333 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 x1)).
Definition term493 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term168 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term254 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1))))) x2.
Definition term26 := (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False.
Definition term435 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term434 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0)).
Definition term413 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)))).
Definition term412 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0)).
Definition term378 := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)))).
Definition term377 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) \/ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) \/ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0)).
Definition term356 (x0 : nat) := @eq Prop (forall y0 : nat, (((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) /\ ((~ ((Nat.modulo x0 y0) = x0)) \/ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)))).
Definition term355 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Nat.modulo x0 y1) = x0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0)).
Definition term322 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) /\ (forall y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0))))).
Definition term321 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) \/ (y2 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) \/ (~ (y2 = (NUMERAL 0)))) y0)).
Definition term300 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0))) /\ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) \/ (~ (y0 = (NUMERAL 0))))).
Definition term299 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) \/ (y1 = (NUMERAL 0))) y0) /\ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0)).
Definition term494 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term336 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) \/ (~ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1))).
Definition term279 (x0 : nat) (x1 : nat) := and ((Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0))).
Definition term509 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = x0) /\ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1))) -> x0 = (Nat.modulo x0 x1).
Definition term287 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term352 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((Nat.modulo x0 y0) = x0)) \/ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))) x1.
Definition term350 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) x1.
Definition term10 := (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term194 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ (x0 (Nat.modulo x1 x2)).
Definition term517 (x0 : nat -> Prop) (x1 : nat) := or (x0 x1).
Definition term241 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (x0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y2 y1)))) y0.
Definition term237 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (x0 (Nat.modulo y3 y1))))) y0.
Definition term445 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term164 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x1) /\ (x0 y1)) y0) /\ ((x1 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x0 (Nat.modulo y0 x1)))).
Definition term491 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term85 (x0 : nat -> Prop) (x1 : nat) := (~ (exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0))) /\ ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1))).
Definition term172 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((Peano.lt x2 x0) /\ (x1 x2)).
Definition term332 (x0 : nat) (x1 : nat) := ~ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1)).
Definition term394 (x0 : nat) (x1 : nat) := and ((Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1)))).
Definition term338 (x0 : nat) (x1 : nat) := and (((Nat.modulo x0 x1) = x0) \/ (~ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1)))).
Definition term229 (x0 : nat -> Prop) := ((fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) x0) \/ ((fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1)))) x0).
Definition term147 (x0 : nat -> Prop) := ((fun y0 : nat -> Prop => exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) x0) \/ ((fun y0 : nat -> Prop => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))) x0).
Definition term42 (x0 : nat) := fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term41 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term88 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0)) /\ (~ ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1)))).
Definition term459 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt x0 y0) x1.
Definition term478 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term31 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term81 (x0 : nat -> Prop) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x0 (Nat.modulo y0 x1))).
Definition term334 (x0 : nat) (x1 : nat) := (~ ((Nat.modulo x0 x1) = x0)) \/ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1)).
Definition term35 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1).
Definition term341 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = x0) \/ ((~ (x1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 x1)))) /\ ((~ ((Nat.modulo x0 x1) = x0)) \/ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1))).
Definition term58 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((Peano.lt x2 x0) /\ (x1 x2)).
Definition term14 := fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0)).
Definition term126 (x0 : nat -> Prop) := @eq Prop (exists y0 : nat, ((exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0))))) \/ ((forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0))))).
Definition term125 (x0 : nat -> Prop) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y1))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, x0 (Nat.modulo y2 y1)))) y0)).
Definition term54 (x0 : nat) (x1 : nat -> Prop) := @eq Prop (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0)).
Definition term337 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) \/ ((~ (x1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 x1))).
Definition term186 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term258 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1)))) x2.
Definition term526 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp (~ ((~ (x2 = x0)) \/ (~ (x1 x2)))).
Definition term70 (x0 : nat -> Prop) (x1 : nat) := ~ (exists y0 : nat, x0 (Nat.modulo y0 x1)).
Definition term484 (x0 : nat) (x1 : nat) := (~ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1))) -> (Nat.modulo x0 x1) = (Nat.modulo x0 x1).
Definition term473 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term189 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 (Nat.modulo y1 x1)) y0.
Definition term16 := forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0)).
Definition term512 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term528 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x0 = x2) /\ (x1 x0)) -> x1 x2.
Definition term306 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))) y0.
Definition term492 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term82 (x0 : nat -> Prop) (x1 : nat) := ~ ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1))).
Definition term193 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) /\ ((fun y0 : nat => x0 (Nat.modulo y0 x1)) x2).
Definition term452 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0))) x0.
Definition term122 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0)))) x1.
Definition term185 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term67 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)).
Definition term252 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 x1) /\ (x0 y1)) /\ ((x1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 x1))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1)))) y0).
Definition term234 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (x0 (Nat.modulo y3 y1))))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (x0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y2 y1)))) y0).
Definition term117 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y1))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, x0 (Nat.modulo y2 y1)))) y0).
Definition term108 (x0 : nat -> Prop) := ~ ((fun y0 : nat -> Prop => forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))) x0).
Definition term544 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term57 := fun y0 : nat -> Prop => forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))).
Definition term209 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1))).
Definition term224 := exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, (forall y4 : nat, (~ (Peano.lt y4 y2)) \/ (~ (y1 y4))) /\ ((~ (y2 = (NUMERAL 0))) /\ (y1 (Nat.modulo y3 y2)))) y0.
Definition term220 := exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, ((Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y4 : nat, ~ (y1 (Nat.modulo y4 y2))))) y0.
Definition term157 := exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y2)) \/ (~ (y1 y3))) /\ ((~ (y2 = (NUMERAL 0))) /\ (exists y3 : nat, y1 (Nat.modulo y3 y2)))) y0.
Definition term152 := exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y1 (Nat.modulo y3 y2))))) y0.
Definition term36 (x0 : nat) := fun y0 : nat => ((Nat.modulo x0 y0) = x0) = ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)).
Definition term7 := (((~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False) -> ((~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False.
Definition term418 (x0 : nat) := and (forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))).
Definition term361 (x0 : nat) := and (forall y0 : nat, ((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))).
Definition term305 (x0 : nat) := and (forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0))).
Definition term84 (x0 : nat) (x1 : nat -> Prop) := and (forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0))).
Definition term462 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term187 (x0 : nat -> Prop) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, (fun y1 : nat => x0 (Nat.modulo y1 x1)) y0).
Definition term12 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL 0)).
Definition term5 := ((~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False.
Definition term340 (x0 : nat) (x1 : nat) := (((Nat.modulo x0 x1) = x0) \/ (~ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1)))) /\ ((~ ((Nat.modulo x0 x1) = x0)) \/ ((x1 = (NUMERAL 0)) \/ (Peano.lt x0 x1))).
Definition term27 := (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ~ ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term215 := (exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) \/ (exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1)))).
Definition term159 := (exists y0 : nat -> Prop, exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) \/ (exists y0 : nat -> Prop, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))).
Definition term405 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0))).
Definition term78 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term534 (x0 : nat -> Prop) (x1 : nat) := imp (~ (~ (x0 x1))).
Definition term407 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1.
Definition term395 (x0 : nat) (x1 : nat) := and ((Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)))).
Definition term349 (x0 : nat) := fun y0 : nat => (~ ((Nat.modulo x0 y0) = x0)) \/ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)).
Definition term419 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0.
Definition term414 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term362 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ ((Nat.modulo x0 y1) = x0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt x0 y1))) y0.
Definition term357 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.modulo x0 y1) = x0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term301 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) \/ (y1 = (NUMERAL 0))) y0.
Definition term79 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term245 (x0 : nat -> Prop) (x1 : nat) := or ((fun y0 : nat => exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) x1).
Definition term497 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term232 := fun y0 : nat -> Prop => (exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) \/ (exists y1 : nat, exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1)))).
Definition term136 := fun y0 : nat -> Prop => (exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))).
Definition term166 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0.
Definition term335 (x0 : nat) (x1 : nat) := or ((Nat.modulo x1 x0) = x1).
Definition term240 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0)))) x1.
Definition term236 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) x1.
Definition term451 := forall y0 : nat, forall y1 : nat, (((Nat.modulo y0 y1) = y0) \/ (~ (y1 = (NUMERAL 0)))) /\ (((Nat.modulo y0 y1) = y0) \/ (~ (Peano.lt y0 y1))).
Definition term443 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term438 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1))).
Definition term401 := forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term386 := forall y0 : nat, forall y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)).
Definition term381 := forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1))).
Definition term345 := forall y0 : nat, forall y1 : nat, (((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) /\ ((~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term330 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0))).
Definition term325 := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0)).
Definition term285 := forall y0 : nat, forall y1 : nat, ((Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) /\ ((~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))).
Definition term45 := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))).
Definition term39 := forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)).
Definition term19 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term216 := (exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, ((Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y4 : nat, ~ (y1 (Nat.modulo y4 y2))))) y0) \/ (exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, (forall y4 : nat, (~ (Peano.lt y4 y2)) \/ (~ (y1 y4))) /\ ((~ (y2 = (NUMERAL 0))) /\ (y1 (Nat.modulo y3 y2)))) y0).
Definition term141 := (exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y1 (Nat.modulo y3 y2))))) y0) \/ (exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y2)) \/ (~ (y1 y3))) /\ ((~ (y2 = (NUMERAL 0))) /\ (exists y3 : nat, y1 (Nat.modulo y3 y2)))) y0).
Definition term65 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0)) x2).
Definition term432 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) x0).
Definition term375 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) x0).
Definition term319 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))) x0).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term60 (x0 : nat -> Prop) := ~ (ex x0).
Definition term6 := (((~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False.
Definition term251 (x0 : nat -> Prop) := exists y0 : nat, (exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0)))).
Definition term253 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => ((Peano.lt y1 x1) /\ (x0 y1)) /\ ((x1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 x1))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1)))) y0).
Definition term235 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, ((Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (x0 (Nat.modulo y3 y1))))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (x0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y2 y1)))) y0).
Definition term116 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y1))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, x0 (Nat.modulo y2 y1)))) y0).
Definition term118 (x0 : nat -> Prop) := fun y0 : nat => (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0)))).
Definition term139 (x0 : type993) (x1 : type993) := (exists y0 : nat -> Prop, x0 y0) \/ (exists y0 : nat -> Prop, x1 y0).
Definition term461 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt x0 y0) x1).
Definition term277 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0)).
Definition term23 := (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False.
Definition term30 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term469 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) \/ (~ (x1 x2)).
Definition term455 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (x0 (Nat.modulo y0 x1))) x2.
Definition term519 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2)))).
Definition term518 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2))).
Definition term61 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term55 (x0 : nat -> Prop) := fun y0 : nat => (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) = ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0))).
Definition term94 (x0 : nat -> Prop) (x1 : nat) := ~ ((exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0)) = ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1)))).
Definition term487 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term247 (x0 : nat -> Prop) (x1 : nat) := ((fun y0 : nat => exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) x1) \/ ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0)))) x1).
Definition term33 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term458 (x0 : nat) := fun y0 : nat => Peano.lt x0 y0.
Definition term228 (x0 : nat -> Prop) := or (exists y0 : nat, exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))).
Definition term472 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2))).
Definition term163 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term2 := (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> False.
Definition term521 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 x0)))) -> x1 x2.
Definition term231 := fun y0 : nat -> Prop => ((fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, ((Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y4 : nat, ~ (y1 (Nat.modulo y4 y2))))) y0) \/ ((fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, (forall y4 : nat, (~ (Peano.lt y4 y2)) \/ (~ (y1 y4))) /\ ((~ (y2 = (NUMERAL 0))) /\ (y1 (Nat.modulo y3 y2)))) y0).
Definition term148 := fun y0 : nat -> Prop => ((fun y1 : nat -> Prop => exists y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y1 (Nat.modulo y3 y2))))) y0) \/ ((fun y1 : nat -> Prop => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y2)) \/ (~ (y1 y3))) /\ ((~ (y2 = (NUMERAL 0))) /\ (exists y3 : nat, y1 (Nat.modulo y3 y2)))) y0).
Definition term56 (x0 : nat -> Prop) := forall y0 : nat, (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) = ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0))).
Definition term391 (x0 : nat) (x1 : nat) := or (Peano.lt x0 (S x1)).
Definition term530 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((x1 = (Nat.modulo x1 x2)) /\ (x0 x1)) -> x0 (Nat.modulo x1 x2).
Definition term4 := (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False.
Definition term410 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1) /\ ((fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))) x1).
Definition term353 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) x1) /\ ((fun y0 : nat => (~ ((Nat.modulo x0 y0) = x0)) \/ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))) x1).
Definition term297 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0))) x1) /\ ((fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) \/ (~ (y0 = (NUMERAL 0)))) x1).
Definition term289 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term138 (x0 : type993) (x1 : type993) := exists y0 : nat -> Prop, (x0 y0) \/ (x1 y0).
Definition term524 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term543 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> x1 = (NUMERAL 0).
Definition term308 (x0 : nat) := forall y0 : nat, (~ (Peano.lt (Nat.modulo x0 y0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term514 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x1 x0) \/ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term490 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term260 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1)))) y0.
Definition term256 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 x1) /\ (x0 y1)) /\ ((x1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 x1))))) y0.
Definition term203 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1))) y0.
Definition term167 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0.
Definition term133 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, x0 (Nat.modulo y2 y1)))) y0.
Definition term128 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y1))))) y0.
Definition term202 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1))) y0.
Definition term480 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term460 (x0 : nat) := (fun y0 : nat => Peano.lt x0 y0) (NUMERAL 0).
Definition term396 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1)))) /\ ((~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term510 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.modulo x0 x1))) -> x0 = (Nat.modulo x0 x1).
Definition term21 := ~ ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term9 := ~ ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term481 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) -> (Nat.modulo x1 x0) = x1.
Definition term388 (x0 : nat) (x1 : nat) := ~ ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term502 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term282 (x0 : nat) := fun y0 : nat => ((Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0))) /\ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term49 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term397 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)))) /\ ((~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term296 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) \/ (~ (y0 = (NUMERAL 0)))) x1.
Definition term170 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x0 (Nat.modulo y0 x1))))).
Definition term169 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Peano.lt y1 x1) /\ (x0 y1)) y0) /\ ((x1 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x0 (Nat.modulo y0 x1))))).
Definition term250 (x0 : nat -> Prop) := fun y0 : nat => (exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0)))).
Definition term90 (x0 : nat -> Prop) (x1 : nat) := or ((exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0)) /\ (~ ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1))))).
Definition term485 (x0 : nat) (x1 : nat) := ~ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1)).
Definition term467 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term422 (x0 : nat) := (forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ (forall y0 : nat, (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term365 (x0 : nat) := (forall y0 : nat, ((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) /\ (forall y0 : nat, (~ ((Nat.modulo x0 y0) = x0)) \/ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))).
Definition term309 (x0 : nat) := (forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0))) /\ (forall y0 : nat, (~ (Peano.lt (Nat.modulo x0 y0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term390 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term149 := @eq Prop (exists y0 : nat -> Prop, ((fun y1 : nat -> Prop => exists y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y1 (Nat.modulo y3 y2))))) y0) \/ ((fun y1 : nat -> Prop => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y2)) \/ (~ (y1 y3))) /\ ((~ (y2 = (NUMERAL 0))) /\ (exists y3 : nat, y1 (Nat.modulo y3 y2)))) y0)).
Definition term272 := fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, (((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) \/ ((forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1)))).
Definition term213 := fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1))).
Definition term180 := fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1)))).
Definition term165 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (Peano.lt y1 x1) /\ (x0 y1)) y0) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1)))).
Definition term11 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term440 := and (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))).
Definition term383 := and (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))).
Definition term327 := and (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))).
Definition term249 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, ((Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (x0 (Nat.modulo y3 y1))))) y0) \/ ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (x0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y2 y1)))) y0).
Definition term520 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2)))).
Definition term447 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term1 := forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))).
Definition term278 (x0 : nat) (x1 : nat) := and ((Peano.lt (Nat.modulo x0 x1) x1) \/ (~ (~ (x1 = (NUMERAL 0))))).
Definition term162 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term43 (x0 : nat) := forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term448 (x0 : nat) := fun y0 : nat => (((Nat.modulo x0 y0) = x0) \/ (~ (y0 = (NUMERAL 0)))) /\ (((Nat.modulo x0 y0) = x0) \/ (~ (Peano.lt x0 y0))).
Definition term416 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0))).
Definition term421 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term364 (x0 : nat) := forall y0 : nat, (~ ((Nat.modulo x0 y0) = x0)) \/ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)).
Definition term71 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, ~ ((fun y1 : nat => x0 (Nat.modulo y1 x1)) y0).
Definition term63 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term441 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0.
Definition term436 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term384 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) \/ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0.
Definition term379 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) \/ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term328 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) \/ (~ (y2 = (NUMERAL 0)))) y0.
Definition term323 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) \/ (y2 = (NUMERAL 0))) y0.
Definition term453 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (((Nat.modulo y0 y1) = y0) \/ (~ (y1 = (NUMERAL 0)))) /\ (((Nat.modulo y0 y1) = y0) \/ (~ (Peano.lt y0 y1)))) x0.
Definition term431 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term429 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0.
Definition term374 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))) x0.
Definition term372 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) x0.
Definition term318 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))) x0.
Definition term316 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) x0.
Definition term339 (x0 : nat) (x1 : nat) := and (((Nat.modulo x0 x1) = x0) \/ ((~ (x1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 x1)))).
Definition term402 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term20 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term52 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) /\ (x1 y0).
Definition term91 (x0 : nat -> Prop) (x1 : nat) := or ((exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x0 (Nat.modulo y0 x1))))).
Definition term87 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0)).
Definition term208 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((fun y1 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1))) y0).
Definition term77 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, ~ (x0 (Nat.modulo y0 x1)).
Definition term221 := or (exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, ((Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y4 : nat, ~ (y1 (Nat.modulo y4 y2))))) y0).
Definition term154 := or (exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y1 (Nat.modulo y3 y2))))) y0).
Definition term392 (x0 : nat) (x1 : nat) := (Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term266 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (((Peano.lt x1 x2) /\ (x0 x1)) /\ ((x2 = (NUMERAL 0)) \/ (forall y0 : nat, ~ (x0 (Nat.modulo y0 x2))))) \/ ((forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x0 y0))) /\ ((~ (x2 = (NUMERAL 0))) /\ (x0 (Nat.modulo x1 x2)))).
Definition term13 := fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False.
Definition term223 := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, (forall y4 : nat, (~ (Peano.lt y4 y2)) \/ (~ (y1 y4))) /\ ((~ (y2 = (NUMERAL 0))) /\ (y1 (Nat.modulo y3 y2)))) y0.
Definition term219 := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, ((Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y4 : nat, ~ (y1 (Nat.modulo y4 y2))))) y0.
Definition term156 := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y2)) \/ (~ (y1 y3))) /\ ((~ (y2 = (NUMERAL 0))) /\ (exists y3 : nat, y1 (Nat.modulo y3 y2)))) y0.
Definition term151 := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => exists y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y1 (Nat.modulo y3 y2))))) y0.
Definition term74 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ (x0 (Nat.modulo x1 x2)).
Definition term37 (x0 : nat) := forall y0 : nat, ((Nat.modulo x0 y0) = x0) = ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0)).
Definition term499 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term409 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term72 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 (Nat.modulo y0 x1)) x2.
Definition term98 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, x0 (Nat.modulo y2 y1)))) y0).
Definition term474 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> Peano.lt x0 x1.
Definition term263 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => ((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1))))) x2).
Definition term230 (x0 : nat -> Prop) := (exists y0 : nat, exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) \/ (exists y0 : nat, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0)))).
Definition term217 := exists y0 : nat -> Prop, ((fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, ((Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y4 : nat, ~ (y1 (Nat.modulo y4 y2))))) y0) \/ ((fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, (forall y4 : nat, (~ (Peano.lt y4 y2)) \/ (~ (y1 y4))) /\ ((~ (y2 = (NUMERAL 0))) /\ (y1 (Nat.modulo y3 y2)))) y0).
Definition term140 := exists y0 : nat -> Prop, ((fun y1 : nat -> Prop => exists y2 : nat, (exists y3 : nat, (Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y1 (Nat.modulo y3 y2))))) y0) \/ ((fun y1 : nat -> Prop => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y2)) \/ (~ (y1 y3))) /\ ((~ (y2 = (NUMERAL 0))) /\ (exists y3 : nat, y1 (Nat.modulo y3 y2)))) y0).
Definition term259 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1)))) y0.
Definition term255 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.lt y1 x1) /\ (x0 y1)) /\ ((x1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 x1))))) y0.
Definition term132 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, x0 (Nat.modulo y2 y1)))) y0.
Definition term127 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y1))))) y0.
Definition term439 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0).
Definition term417 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0).
Definition term382 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) \/ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0).
Definition term360 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Nat.modulo x0 y1) = x0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y1)))) y0).
Definition term326 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) \/ (y2 = (NUMERAL 0))) y0).
Definition term304 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) \/ (y1 = (NUMERAL 0))) y0).
Definition term476 (x0 : nat) (x1 : nat) := (~ (~ (Peano.lt x1 x0))) -> (Nat.modulo x1 x0) = x1.
Definition term471 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term430 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0).
Definition term373 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) x0).
Definition term317 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) x0).
Definition term449 (x0 : nat) := forall y0 : nat, (((Nat.modulo x0 y0) = x0) \/ (~ (y0 = (NUMERAL 0)))) /\ (((Nat.modulo x0 y0) = x0) \/ (~ (Peano.lt x0 y0))).
Definition term283 (x0 : nat) := forall y0 : nat, ((Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0))) /\ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) \/ (~ (y0 = (NUMERAL 0)))).
Definition term47 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => x0 (Nat.modulo y0 x1).
Definition term40 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term53 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0).
Definition term398 (x0 : nat) := fun y0 : nat => ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term210 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1))).
Definition term120 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0))))) x1.
Definition term533 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (~ (x0 x1))) -> ~ (Peano.lt x1 x2).
Definition term537 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 (Nat.modulo x1 x2)) -> ~ (Peano.lt (Nat.modulo x1 x2) x2).
Definition term119 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0))).
Definition term463 (x0 : nat) := (~ (Peano.lt x0 (NUMERAL 0))) -> Peano.lt x0 (NUMERAL 0).
Definition term546 := ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False.
Definition term8 := ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> False.
Definition term102 (x0 : nat -> Prop) := fun y0 : nat => ((exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0))))) \/ ((forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0)))).
Definition term315 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0))).
Definition term44 := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))).
Definition term205 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0))) /\ (exists y0 : nat, (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1)))).
Definition term204 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0))) /\ (exists y0 : nat, (fun y1 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1))) y0)).
Definition term506 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term286 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term242 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (x0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y2 y1)))) y0.
Definition term238 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (x0 (Nat.modulo y3 y1))))) y0.
Definition term525 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (x2 = x0) /\ (x1 x2).
Definition term271 (x0 : nat -> Prop) := exists y0 : nat, exists y1 : nat, (((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) \/ ((forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0)))).
Definition term212 (x0 : nat -> Prop) := exists y0 : nat, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0))).
Definition term179 (x0 : nat -> Prop) := exists y0 : nat, exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0)))).
Definition term176 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1)))).
Definition term424 := forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term367 := forall y0 : nat, (forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term311 := forall y0 : nat, (forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) /\ (forall y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))).
Definition term107 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))) x0.
Definition term75 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 (Nat.modulo y1 x1)) y0).
Definition term114 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term86 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0))) /\ ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1))).
Definition term48 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, x0 (Nat.modulo y0 x1).
Definition term105 (x0 : type993) := exists y0 : nat -> Prop, ~ (x0 y0).
Definition term408 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1).
Definition term351 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) x1).
Definition term295 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0))) x1).
Definition term101 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, x0 (Nat.modulo y2 y1)))) y0).
Definition term66 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt y1 x0) /\ (x1 y1)) y0).
Definition term292 (x0 : nat) := fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) \/ (y0 = (NUMERAL 0)).
Definition term100 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) = ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0)))) x1).
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term486 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term267 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.lt y1 x1) /\ (x0 y1)) /\ ((x1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 x1))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1)))) y0).
Definition term124 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y1))))) y0) \/ ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (x0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, x0 (Nat.modulo y2 y1)))) y0).
Definition term92 (x0 : nat -> Prop) (x1 : nat) := ((exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0)) /\ (~ ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1))))) \/ ((~ (exists y0 : nat, (Peano.lt y0 x1) /\ (x0 y0))) /\ ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1)))).
Definition term257 (x0 : nat -> Prop) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 x1) /\ (x0 y1)) /\ ((x1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 x1))))) y0).
Definition term239 (x0 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (x0 (Nat.modulo y3 y1))))) y0).
Definition term130 (x0 : nat -> Prop) := or (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, (Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y1))))) y0).
Definition term69 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term73 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x0 (Nat.modulo y0 x1)) x2).
Definition term515 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (x2 = x0)) \/ (~ (x1 x2)).
Definition term59 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.lt x2 x0)) \/ (~ (x1 x2)).
Definition term50 (x0 : nat -> Prop) (x1 : nat) := (~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1)).
Definition term501 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term222 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1)))) x0.
Definition term218 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) x0.
Definition term51 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) /\ (x1 x2).
Definition term123 (x0 : nat -> Prop) (x1 : nat) := ((fun y0 : nat => (exists y1 : nat, (Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 y0))))) x1) \/ ((fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1))) /\ ((~ (y0 = (NUMERAL 0))) /\ (exists y1 : nat, x0 (Nat.modulo y1 y0)))) x1).
Definition term508 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = x0) /\ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1)).
Definition term465 (x0 : nat) := (Peano.lt x0 (NUMERAL 0)) -> False.
Definition term489 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term532 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 (Nat.modulo x1 x2)) -> False.
Definition term196 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1)).
Definition term483 (x0 : nat) (x1 : nat) := ~ ((Nat.modulo x1 x0) = x1).
Definition term442 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0.
Definition term437 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term385 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ ((Nat.modulo y1 y2) = y1)) \/ ((y2 = (NUMERAL 0)) \/ (Peano.lt y1 y2))) y0.
Definition term380 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.modulo y1 y2) = y1) \/ ((~ (y2 = (NUMERAL 0))) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term329 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) \/ (~ (y2 = (NUMERAL 0)))) y0.
Definition term324 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) \/ (y2 = (NUMERAL 0))) y0.
Definition term25 := imp (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))).
Definition term22 := imp (forall y0 : nat, forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term195 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (x1 = (NUMERAL 0))) /\ ((fun y1 : nat => x0 (Nat.modulo y1 x1)) y0).
Definition term268 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1))))) \/ ((forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1)))).
Definition term342 (x0 : nat) := fun y0 : nat => (((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) /\ ((~ ((Nat.modulo x0 y0) = x0)) \/ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term527 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((x2 = x0) /\ (x1 x2)).
Definition term507 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term199 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0))) /\ (exists y0 : nat, (fun y1 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1))) y0).
Definition term96 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term190 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 (Nat.modulo y1 x1)) y0.
Definition term206 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0))) /\ ((fun y0 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1))) x2).
Definition term293 (x0 : nat) := fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) \/ (~ (y0 = (NUMERAL 0))).
Definition term62 (x0 : nat) (x1 : nat -> Prop) := ~ (exists y0 : nat, (Peano.lt y0 x0) /\ (x1 y0)).
Definition term450 := fun y0 : nat => forall y1 : nat, (((Nat.modulo y0 y1) = y0) \/ (~ (y1 = (NUMERAL 0)))) /\ (((Nat.modulo y0 y1) = y0) \/ (~ (Peano.lt y0 y1))).
Definition term428 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term427 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1))).
Definition term400 := fun y0 : nat => forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term371 := fun y0 : nat => forall y1 : nat, (~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)).
Definition term370 := fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1))).
Definition term344 := fun y0 : nat => forall y1 : nat, (((Nat.modulo y0 y1) = y0) \/ ((~ (y1 = (NUMERAL 0))) /\ (~ (Peano.lt y0 y1)))) /\ ((~ ((Nat.modulo y0 y1) = y0)) \/ ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1))).
Definition term314 := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0)).
Definition term284 := fun y0 : nat => forall y1 : nat, ((Peano.lt (Nat.modulo y0 y1) y1) \/ (y1 = (NUMERAL 0))) /\ ((~ (Peano.lt (Nat.modulo y0 y1) y1)) \/ (~ (y1 = (NUMERAL 0)))).
Definition term38 := fun y0 : nat => forall y1 : nat, ((Nat.modulo y0 y1) = y0) = ((y1 = (NUMERAL 0)) \/ (Peano.lt y0 y1)).
Definition term34 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term115 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term399 (x0 : nat) := forall y0 : nat, ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term343 (x0 : nat) := forall y0 : nat, (((Nat.modulo x0 y0) = x0) \/ ((~ (y0 = (NUMERAL 0))) /\ (~ (Peano.lt x0 y0)))) /\ ((~ ((Nat.modulo x0 y0) = x0)) \/ ((y0 = (NUMERAL 0)) \/ (Peano.lt x0 y0))).
Definition term468 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x1 x2) = (x1 x0)) -> (x1 x0) \/ (~ (x1 x2)).
Definition term28 := imp (~ (forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) = ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1))))).
Definition term540 (x0 : Prop) := x0 -> ~ x0.
Definition term276 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) \/ (~ (~ (x1 = (NUMERAL 0)))).
Definition term192 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, x0 (Nat.modulo y0 x1))).
Definition term191 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((~ (x1 = (NUMERAL 0))) /\ (exists y0 : nat, (fun y1 : nat => x0 (Nat.modulo y1 x1)) y0)).
Definition term539 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) -> ~ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term479 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.lt x0 x1))).
Definition term200 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((fun y1 : nat => (~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1))) y0).
Definition term68 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)).
Definition term146 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2))) /\ ((~ (y1 = (NUMERAL 0))) /\ (exists y2 : nat, y0 (Nat.modulo y2 y1)))) x0.
Definition term144 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat, (exists y2 : nat, (Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (y0 (Nat.modulo y2 y1))))) x0.
Definition term188 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (~ (x1 = (NUMERAL 0))) /\ ((fun y1 : nat => x0 (Nat.modulo y1 x1)) y0).
Definition term262 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, ((Peano.lt y0 x1) /\ (x0 y0)) /\ ((x1 = (NUMERAL 0)) \/ (forall y1 : nat, ~ (x0 (Nat.modulo y1 x1))))) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y0 x1))))).
Definition term261 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ((Peano.lt y1 x1) /\ (x0 y1)) /\ ((x1 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 x1))))) y0) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2))) /\ ((~ (x1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 x1)))) y0)).
Definition term244 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, exists y1 : nat, ((Peano.lt y1 y0) /\ (x0 y1)) /\ ((y0 = (NUMERAL 0)) \/ (forall y2 : nat, ~ (x0 (Nat.modulo y2 y0))))) \/ (exists y0 : nat, exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y2 y0)) \/ (~ (x0 y2))) /\ ((~ (y0 = (NUMERAL 0))) /\ (x0 (Nat.modulo y1 y0))))).
Definition term243 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.lt y2 y1) /\ (x0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (x0 (Nat.modulo y3 y1))))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (x0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (x0 (Nat.modulo y2 y1)))) y0)).
Definition term226 := @eq Prop ((exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, ((Peano.lt y2 y1) /\ (y0 y2)) /\ ((y1 = (NUMERAL 0)) \/ (forall y3 : nat, ~ (y0 (Nat.modulo y3 y1))))) \/ (exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, (forall y3 : nat, (~ (Peano.lt y3 y1)) \/ (~ (y0 y3))) /\ ((~ (y1 = (NUMERAL 0))) /\ (y0 (Nat.modulo y2 y1))))).
Definition term225 := @eq Prop ((exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, ((Peano.lt y3 y2) /\ (y1 y3)) /\ ((y2 = (NUMERAL 0)) \/ (forall y4 : nat, ~ (y1 (Nat.modulo y4 y2))))) y0) \/ (exists y0 : nat -> Prop, (fun y1 : nat -> Prop => exists y2 : nat, exists y3 : nat, (forall y4 : nat, (~ (Peano.lt y4 y2)) \/ (~ (y1 y4))) /\ ((~ (y2 = (NUMERAL 0))) /\ (y1 (Nat.modulo y3 y2)))) y0)).
