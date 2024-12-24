Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term287 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (x0 y1)) /\ (forall y2 : nat, (~ (Peano.le y2 y1)) -> x0 y2)) y0.
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((fun y0 : a0 => (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) x1) \/ ((fun y0 : a0 => (~ (x0 y0)) /\ (forall y1 : a0, x0 y1)) x1).
Definition term542 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, x0 y0) /\ (~ (x0 x1)).
Definition term226 (x0 : nat -> Prop) := ~ (exists y0 : nat, ~ (x0 y0)).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or ((forall y0 : a0, x0 y0) /\ (~ (x0 x1))).
Definition term273 (x0 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1) /\ (~ (exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1))).
Definition term272 (x0 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0) /\ (~ (exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0))).
Definition term528 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term375 (x0 : nat -> Prop) := ~ (all x0).
Definition term188 := (~ False) -> False.
Definition term480 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)).
Definition term231 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term557 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (x1 y0)) x2.
Definition term548 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (x1 y0)) x2.
Definition term347 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term59 (x0 : Prop) := imp (~ x0).
Definition term208 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0.
Definition term207 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (Nat.add y0 (NUMERAL (BIT1 0))))) -> x1 y0.
Definition term373 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((Peano.lt x0 x2) -> x1 x2).
Definition term335 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term625 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, (Peano.le y0 y1) -> x0 y1) -> (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (S y1))) -> x0 y1) -> (~ ((exists y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) /\ (forall y1 : nat, (forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) -> x0 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> ((forall y1 : nat, (Peano.lt y1 (NUMERAL 0)) = False) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 (S y2)) = ((y1 = y2) \/ (Peano.lt y1 y2)))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) -> False) x1.
Definition term597 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) \/ (~ (Peano.lt x1 x2)).
Definition term575 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term267 (x0 : nat) (x1 : nat -> Prop) := (~ (x1 x0)) /\ (forall y0 : nat, (~ (Peano.le y0 x0)) -> x1 y0).
Definition term594 (x0 : nat) := Peano.lt x0 (S x0).
Definition term520 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term498 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term280 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1.
Definition term264 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1.
Definition term248 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0.
Definition term247 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, ((fun y2 : nat => ~ (x0 y2)) y1) -> Peano.le y1 y0.
Definition term473 (x0 : nat -> Prop) := exists y0 : nat -> nat, exists y1 : nat, (forall y2 : nat, (Peano.lt y2 (y0 y2)) /\ (~ (x0 (y0 y2)))) \/ ((forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x0 y2)) /\ (~ (x0 y1))).
Definition term249 (x0 : nat -> Prop) := (exists y0 : nat, ~ (x0 y0)) /\ (exists y0 : nat, forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0).
Definition term260 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.le x2 x0)) -> x1 x2.
Definition term401 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0) x1.
Definition term182 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0) \/ ((fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0).
Definition term47 (x0 : Prop) := ~ (~ x0).
Definition term227 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0) /\ (exists y0 : nat, forall y1 : nat, ((fun y2 : nat => ~ (x0 y2)) y1) -> Peano.le y1 y0).
Definition term92 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => ((exists y1 : nat, y0 y1) /\ (exists y1 : nat, forall y2 : nat, (y0 y2) -> Peano.le y2 y1)) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (y0 y2) -> Peano.le y2 y1))) x0.
Definition term369 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ ((Peano.lt x2 x0) /\ (x1 (S x2)))) \/ (x1 x2).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term393 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (x1 y0).
Definition term364 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (x1 y0).
Definition term281 (x0 : nat -> Prop) := and (exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1).
Definition term266 (x0 : nat -> Prop) := and (exists y0 : nat, forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1).
Definition term265 (x0 : nat -> Prop) := and (exists y0 : nat, forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0).
Definition term93 (x0 : nat -> Prop) := (exists y0 : nat, x0 y0) /\ (exists y0 : nat, forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term571 (x0 : nat -> nat) (x1 : nat) := (Peano.lt x1 (x0 x1)) -> Peano.le x1 (x0 x1).
Definition term572 (x0 : nat -> nat) (x1 : nat) := Peano.le x1 (x0 x1).
Definition term196 (x0 : nat -> Prop) (x1 : nat) := x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term425 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (Peano.lt y0 y1) /\ (~ (x0 y1))) x2 (x1 x2).
Definition term381 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt x0 y0) /\ (~ (x1 y0)).
Definition term81 (x0 : Prop) := False /\ (~ x0).
Definition term414 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) /\ (~ (x0 y3))) y0 y1.
Definition term412 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term390 (x0 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (~ (x0 y1)).
Definition term53 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ (~ x1)) -> ((x2 /\ x0) = x1) -> ~ x2.
Definition term506 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term453 (x0 : nat -> Prop) := fun y0 : nat -> nat => ((fun y1 : nat -> nat => forall y2 : nat, (Peano.lt y2 (y1 y2)) /\ (~ (x0 (y1 y2)))) y0) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x0 y2)) /\ (~ (x0 y1))).
Definition term441 (x0 : nat -> Prop) := (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (Peano.lt y2 (y1 y2)) /\ (~ (x0 (y1 y2)))) y0) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x0 y1)) /\ (~ (x0 y0))).
Definition term484 (x0 : nat) (x1 : nat) := (Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1))).
Definition term290 (x0 : nat -> Prop) := @eq Prop (~ (exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1))).
Definition term289 (x0 : nat -> Prop) := @eq Prop (~ (exists y0 : nat, (fun y1 : nat => (~ (x0 y1)) /\ (forall y2 : nat, (~ (Peano.le y2 y1)) -> x0 y2)) y0)).
Definition term552 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => ((~ (Peano.lt y0 x0)) \/ (~ (x1 (S y0)))) \/ (x1 y0)) x2.
Definition term574 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le x1 (x0 x1)).
Definition term330 (x0 : nat -> Prop) := imp (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0))).
Definition term230 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 y0)) x1.
Definition term202 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((Peano.lt x2 x0) /\ (x1 (S x2))).
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term141 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term391 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.lt x0 x2)) \/ (x1 x2).
Definition term362 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (x1 x2).
Definition term255 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) /\ (forall y0 : nat, (~ (x0 y0)) -> Peano.le y0 x1).
Definition term74 (x0 : Prop) := imp (x0 = True).
Definition term461 (x0 : nat -> nat) (x1 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (Peano.lt y1 (x0 y1)) /\ (~ (x1 (x0 y1)))) \/ ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x1 y2)) /\ (~ (x1 y1))) y0).
Definition term475 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term91 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x0 /\ (~ x1)) -> ((x2 /\ x0) = x1) -> ~ x2) -> (x0 /\ (~ x1)) -> ((x2 /\ x0) = x1) -> ~ x2.
Definition term601 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (S x1)) -> x0 (S x1).
Definition term609 (x0 : nat -> Prop) (x1 : nat) := (~ (~ (x0 (S x1)))) /\ (~ (x0 x1)).
Definition term56 (x0 : Prop) (x1 : Prop) := (False /\ (~ x0)) -> ((x1 /\ False) = x0) -> ~ x1.
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term563 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.lt x1 (x0 x1))) -> Peano.lt x1 (x0 x1).
Definition term337 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term305 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term119 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term17 (x0 : Prop) := ~ ((~ False) /\ x0).
Definition term12 (x0 : Prop) := ~ ((~ True) /\ x0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (~ (x0 y0)) /\ (forall y1 : a0, x0 y1)) x1.
Definition term315 := and (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False).
Definition term587 (x0 : nat) := ~ (x0 = x0).
Definition term90 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x0 /\ (~ x1)) -> ((x2 /\ x0) = x1) -> ~ x2) -> ((x2 /\ x0) = x1) -> ~ x2.
Definition term137 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term192 := fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term42 (x0 : Prop) := (~ x0) -> False.
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) x1.
Definition term521 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0).
Definition term499 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0).
Definition term539 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term437 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term387 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) x1).
Definition term82 (x0 : Prop) := imp (False /\ (~ x0)).
Definition term501 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term83 (x0 : Prop) := @eq Prop (x0 /\ False).
Definition term472 (x0 : nat -> Prop) := fun y0 : nat -> nat => exists y1 : nat, (forall y2 : nat, (Peano.lt y2 (y0 y2)) /\ (~ (x0 (y0 y2)))) \/ ((forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x0 y2)) /\ (~ (x0 y1))).
Definition term193 := forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term62 (x0 : Prop) (x1 : Prop) := imp (x0 = x1).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, x0 y0.
Definition term40 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = ((~ x0) -> y0)) False.
Definition term286 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1)) x1.
Definition term127 (a0 : Type') (x0 : a0 -> Prop) := (~ (forall y0 : a0, x0 y0)) /\ (~ (exists y0 : a0, ~ (x0 y0))).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0).
Definition term515 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0.
Definition term510 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term374 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x0 x2) /\ (~ (x1 x2)).
Definition term419 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.lt x0 y0) /\ (~ (x1 y0))) x2.
Definition term459 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term418 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (Peano.lt y0 y1) /\ (~ (x0 y1))) x1 x2.
Definition term544 (x0 : nat) := fun y0 : nat => ((Peano.lt x0 (S y0)) \/ (~ (x0 = y0))) /\ ((Peano.lt x0 (S y0)) \/ (~ (Peano.lt x0 y0))).
Definition term228 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => ~ (x0 y1)) y0) /\ (forall y1 : nat, ((fun y2 : nat => ~ (x0 y2)) y1) -> Peano.le y1 y0).
Definition term554 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term605 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (S x1))) \/ (x0 x1).
Definition term216 (x0 : nat) (x1 : nat -> Prop) := ((forall y0 : nat, (Peano.le x0 y0) -> x1 y0) /\ (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0)) -> forall y0 : nat, x1 y0.
Definition term215 (x0 : nat) (x1 : nat -> Prop) := ((forall y0 : nat, (Peano.le x0 y0) -> x1 y0) /\ (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (Nat.add y0 (NUMERAL (BIT1 0))))) -> x1 y0)) -> forall y0 : nat, x1 y0.
Definition term23 (x0 : Prop) := @eq Prop (~ ((~ False) /\ x0)).
Definition term20 (x0 : Prop) := @eq Prop (~ ((~ True) /\ x0)).
Definition term603 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> ~ (x0 x1).
Definition term38 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term496 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term600 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (Peano.lt x0 x2))) -> x1 x2.
Definition term578 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (~ (Peano.le x0 x2))) -> x1 x2.
Definition term130 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (~ (~ (exists y0 : a0, ~ (x0 y0)))).
Definition term469 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.lt y1 (x0 y1)) /\ (~ (x1 (x0 y1)))) \/ ((fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x1 y2)) /\ (~ (x1 y1))) y0).
Definition term399 (x0 : nat -> Prop) := ~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0).
Definition term376 (x0 : nat) (x1 : nat -> Prop) := ~ (forall y0 : nat, (Peano.lt x0 y0) -> x1 y0).
Definition term239 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((fun y0 : nat => ~ (x0 y0)) x1) -> Peano.le x1 x2.
Definition term299 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (Peano.lt x1 y0) -> x0 y0) -> x0 x1.
Definition term296 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (~ (Peano.le y0 x1)) -> x0 y0) -> x0 x1.
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term518 := fun y0 : nat => (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term323 := ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term439 (x0 : type1002) (x1 : Prop) := (exists y0 : nat -> nat, x0 y0) \/ x1.
Definition term136 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term341 (x0 : nat -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) -> x0 y1) -> (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (S y1))) -> x0 y1) -> (~ ((exists y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) /\ (forall y1 : nat, (forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) -> x0 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> ((forall y1 : nat, ~ (Peano.lt y1 (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 (S y2)) = ((y1 = y2) \/ (Peano.lt y1 y2)))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)).
Definition term340 (x0 : nat -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.le y0 y1) -> x0 y1) -> (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (S y1))) -> x0 y1) -> (~ ((exists y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) /\ (forall y1 : nat, (forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) -> x0 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> ((forall y1 : nat, (Peano.lt y1 (NUMERAL 0)) = False) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 (S y2)) = ((y1 = y2) \/ (Peano.lt y1 y2)))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) -> False.
Definition term614 (x0 : nat -> Prop) (x1 : nat) := imp (~ ((~ (x0 (S x1))) \/ (x0 x1))).
Definition term316 := and (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term276 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x0 x2) -> x1 x2.
Definition term595 (x0 : nat) := (~ (Peano.lt x0 (S x0))) -> Peano.lt x0 (S x0).
Definition term339 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.le y0 y1) -> x0 y1) -> (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (S y1))) -> x0 y1) -> (~ ((exists y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) /\ (forall y1 : nat, (forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) -> x0 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> ((forall y1 : nat, ~ (Peano.lt y1 (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 (S y2)) = ((y1 = y2) \/ (Peano.lt y1 y2)))) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)).
Definition term338 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.le y0 y1) -> x0 y1) -> (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (S y1))) -> x0 y1) -> (~ ((exists y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) /\ (forall y1 : nat, (forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) -> x0 y1))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> Peano.le y1 y2) -> ((forall y1 : nat, (Peano.lt y1 (NUMERAL 0)) = False) /\ (forall y1 : nat, forall y2 : nat, (Peano.lt y1 (S y2)) = ((y1 = y2) \/ (Peano.lt y1 y2)))) -> (forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) -> False.
Definition term366 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.lt x2 x0)) \/ (~ (x1 (S x2))).
Definition term404 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x0 y1)) /\ (~ (x0 y0)).
Definition term581 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term455 (x0 : nat -> Prop) := exists y0 : nat -> nat, (forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1)))) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x0 y2)) /\ (~ (x0 y1))).
Definition term220 (x0 : nat -> Prop) := forall y0 : nat, ((forall y1 : nat, (Peano.le y0 y1) -> x0 y1) /\ (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (S y1))) -> x0 y1)) -> forall y1 : nat, x0 y1.
Definition term219 (x0 : nat -> Prop) := forall y0 : nat, ((forall y1 : nat, (Peano.le y0 y1) -> x0 y1) /\ (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (Nat.add y1 (NUMERAL (BIT1 0))))) -> x0 y1)) -> forall y1 : nat, x0 y1.
Definition term371 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((~ (Peano.lt y0 x0)) \/ (~ (x1 (S y0)))) \/ (x1 y0).
Definition term186 (x0 : Prop) := (~ x0) -> x0.
Definition term167 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0) \/ (exists y0 : a0, (fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0).
Definition term567 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x0 x1) \/ (~ (Peano.lt x0 x1))).
Definition term236 (x0 : nat -> Prop) := and (exists y0 : nat, ~ (x0 y0)).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => x0 y1) y0).
Definition term15 (x0 : Prop) (x1 : Prop) := @eq Prop ((~ ((~ x1) /\ x0)) = (x0 -> x1)).
Definition term64 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> ~ x1.
Definition term325 := ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term313 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term163 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (~ (x0 y0)) /\ (forall y1 : a0, x0 y1).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) := and (exists y0 : a0, ~ (x0 y0)).
Definition term352 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term607 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term586 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term389 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (Peano.lt y0 y1) /\ (~ (x0 y1)).
Definition term410 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term41 (x0 : Prop) := (~ False) -> x0.
Definition term294 (x0 : nat -> Prop) := fun y0 : nat => ~ ((~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1)).
Definition term621 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term235 (x0 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0).
Definition term326 := ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term428 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (Peano.lt y1 y2) /\ (~ (x0 y2))) y0 (x1 y0).
Definition term435 (x0 : nat -> Prop) := or (exists y0 : nat -> nat, forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1)))).
Definition term240 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x0 x1)) -> Peano.le x1 x2.
Definition term530 := @eq Prop (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term529 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0)).
Definition term508 (x0 : nat) := @eq Prop (forall y0 : nat, ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)))).
Definition term507 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0) /\ ((fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0)).
Definition term434 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1))).
Definition term415 (x0 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) /\ (~ (x0 y3))) y1 (y0 y1).
Definition term413 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, x0 y0) /\ ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term495 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term550 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0)) x1.
Definition term356 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term318 := (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term417 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (Peano.lt y0 y1) /\ (~ (x0 y1))) x1.
Definition term174 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0.
Definition term623 (x0 : nat -> Prop) (x1 : nat) := (x0 x1) -> False.
Definition term108 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term540 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term256 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => ~ (x0 y1)) y0) /\ (forall y1 : nat, ((fun y2 : nat => ~ (x0 y2)) y1) -> Peano.le y1 y0).
Definition term160 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (x1 x0)) /\ (forall y0 : a0, x1 y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term436 (x0 : nat -> Prop) := (exists y0 : nat -> nat, forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1)))) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x0 y1)) /\ (~ (x0 y0))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term462 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x0 y1)) /\ (~ (x0 y0))) x1.
Definition term386 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) x1.
Definition term620 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) -> Peano.le x0 x1.
Definition term562 (x0 : nat -> nat) (x1 : nat) := Peano.lt x1 (x0 x1).
Definition term485 (x0 : nat) (x1 : nat) := and ((Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1)))).
Definition term237 (x0 : nat -> Prop) (x1 : nat) := imp ((fun y0 : nat => ~ (x0 y0)) x1).
Definition term470 (x0 : nat -> nat) (x1 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.lt y1 (x0 y1)) /\ (~ (x1 (x0 y1)))) \/ ((forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x1 y1)) /\ (~ (x1 y0))).
Definition term203 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((Peano.lt x2 x0) /\ (x1 (Nat.add x2 (NUMERAL (BIT1 0))))) -> x1 x2.
Definition term460 (x0 : nat -> nat) (x1 : nat -> Prop) := (forall y0 : nat, (Peano.lt y0 (x0 y0)) /\ (~ (x1 (x0 y0)))) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x1 y2)) /\ (~ (x1 y1))) y0).
Definition term612 (x0 : nat -> Prop) (x1 : nat) := and (x0 (S x1)).
Definition term477 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1).
Definition term358 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term349 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term246 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0.
Definition term245 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, ((fun y2 : nat => ~ (x0 y2)) y1) -> Peano.le y1 y0.
Definition term569 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term351 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term79 (x0 : Prop) := (x0 = False) -> ~ x0.
Definition term195 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0)) x0.
Definition term443 (x0 : nat -> Prop) (x1 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1)))) x1.
Definition term138 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term565 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ (~ (Peano.lt x0 x1)).
Definition term86 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term348 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term454 (x0 : nat -> Prop) := fun y0 : nat -> nat => (forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1)))) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x0 y2)) /\ (~ (x0 y1))).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0.
Definition term171 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0.
Definition term312 := fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0)).
Definition term568 (x0 : nat) (x1 : nat) := (~ (~ (Peano.lt x0 x1))) -> Peano.le x0 x1.
Definition term259 (x0 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0) /\ (~ (exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0)))) -> (((exists y0 : nat, ~ (x0 y0)) /\ (exists y0 : nat, forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0)) = (exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0))) -> ~ (exists y0 : nat, ~ (x0 y0)).
Definition term233 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0.
Definition term148 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, x0 y1) /\ (~ (x0 y0)).
Definition term558 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := ~ (x0 (x1 x2)).
Definition term611 (x0 : nat -> Prop) (x1 : nat) := and (~ (~ (x0 (S x1)))).
Definition term314 := forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0)).
Definition term622 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term241 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => ~ (x0 y1)) y0) -> Peano.le y0 x1.
Definition term420 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (Peano.lt y1 y2) /\ (~ (x0 y2))) x1 y0.
Definition term541 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (S x1)) \/ (~ (x0 = x1))) /\ ((Peano.lt x0 (S x1)) \/ (~ (Peano.lt x0 x1))).
Definition term561 (x0 : nat) (x1 : nat) := (Peano.lt x0 (S x1)) \/ (~ (x0 = x1)).
Definition term331 (x0 : nat -> Prop) := (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term98 (a0 : Type') (x0 : a0 -> Prop) := ~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0)))).
Definition term28 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term253 (x0 : nat -> Prop) (x1 : nat) := and (~ (x0 x1)).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, x0 y1) /\ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term251 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, ~ (x0 y0)) /\ (exists y0 : nat, forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0)).
Definition term250 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ~ (x0 y1)) y0) /\ (exists y0 : nat, forall y1 : nat, ((fun y2 : nat => ~ (x0 y2)) y1) -> Peano.le y1 y0)).
Definition term238 (x0 : nat -> Prop) (x1 : nat) := imp (~ (x0 x1)).
Definition term322 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term153 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => ~ (x0 y1)) y0) /\ (forall y1 : a0, x0 y1).
Definition term106 (a0 : Type') := forall y0 : a0 -> Prop, (forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))).
Definition term60 (x0 : Prop) := @eq Prop (x0 /\ True).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) := and (forall y0 : a0, x0 y0).
Definition term463 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x0 y2)) /\ (~ (x0 y1))) y0.
Definition term596 (x0 : nat) := ~ (Peano.lt x0 (S x0)).
Definition term433 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1))).
Definition term432 (x0 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) /\ (~ (x0 y3))) y1 (y0 y1).
Definition term343 := fun y0 : nat -> Prop => forall y1 : nat, (forall y2 : nat, (Peano.le y1 y2) -> y0 y2) -> (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (S y2))) -> y0 y2) -> (~ ((exists y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) /\ (forall y2 : nat, (forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) -> y0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> ((forall y2 : nat, ~ (Peano.lt y2 (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 (S y3)) = ((y2 = y3) \/ (Peano.lt y2 y3)))) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ (Peano.le y3 y2)).
Definition term342 := fun y0 : nat -> Prop => forall y1 : nat, (forall y2 : nat, (Peano.le y1 y2) -> y0 y2) -> (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (S y2))) -> y0 y2) -> (~ ((exists y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) /\ (forall y2 : nat, (forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) -> y0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> ((forall y2 : nat, (Peano.lt y2 (NUMERAL 0)) = False) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 (S y3)) = ((y2 = y3) \/ (Peano.lt y2 y3)))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ (Peano.le y3 y2)) -> False.
Definition term222 := fun y0 : nat -> Prop => forall y1 : nat, ((forall y2 : nat, (Peano.le y1 y2) -> y0 y2) /\ (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (S y2))) -> y0 y2)) -> forall y2 : nat, y0 y2.
Definition term221 := fun y0 : nat -> Prop => forall y1 : nat, ((forall y2 : nat, (Peano.le y1 y2) -> y0 y2) /\ (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (Nat.add y2 (NUMERAL (BIT1 0))))) -> y0 y2)) -> forall y2 : nat, y0 y2.
Definition term87 (x0 : Prop) (x1 : Prop) := False -> (~ x0) -> ~ x1.
Definition term583 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := x0 (x1 x2).
Definition term445 (x0 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (Peano.lt y2 (y1 y2)) /\ (~ (x0 (y1 y2)))) y0.
Definition term133 (a0 : Type') (x0 : a0 -> Prop) := or ((forall y0 : a0, x0 y0) /\ (exists y0 : a0, ~ (x0 y0))).
Definition term405 (x0 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x0 y1)) /\ (~ (x0 y0)).
Definition term598 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (Peano.lt x0 x2)) \/ (x1 x2)).
Definition term576 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((~ (Peano.le x0 x2)) \/ (x1 x2)).
Definition term424 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (~ (x0 y1))).
Definition term423 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) /\ (~ (x0 y3))) y0 y1).
Definition term336 (x0 : nat) (x1 : nat -> Prop) := imp (forall y0 : nat, (Peano.le x0 y0) -> x1 y0).
Definition term333 (x0 : nat) (x1 : nat -> Prop) := imp (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0).
Definition term298 (x0 : nat) (x1 : nat -> Prop) := imp (forall y0 : nat, (Peano.lt x0 y0) -> x1 y0).
Definition term297 (x0 : nat) (x1 : nat -> Prop) := imp (forall y0 : nat, (~ (Peano.le y0 x0)) -> x1 y0).
Definition term513 (x0 : nat) := and (forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))).
Definition term395 (x0 : nat) (x1 : nat -> Prop) := and (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (x1 y0)).
Definition term394 (x0 : nat) (x1 : nat -> Prop) := and (forall y0 : nat, (Peano.lt x0 y0) -> x1 y0).
Definition term209 (x0 : nat) (x1 : nat -> Prop) := and (forall y0 : nat, (Peano.le x0 y0) -> x1 y0).
Definition term310 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL 0)).
Definition term591 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term49 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (y0 /\ (~ x0)) -> ((x1 /\ y0) = x0) -> ~ x1) x2.
Definition term560 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 (S x1)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) := ((~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False.
Definition term500 (x0 : nat) := fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0))).
Definition term416 (x0 : nat -> Prop) := fun y0 : nat => fun y1 : nat => (Peano.lt y0 y1) /\ (~ (x0 y1)).
Definition term502 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1.
Definition term73 (x0 : Prop) := (~ False) -> (x0 = False) -> ~ x0.
Definition term321 := imp ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term320 := imp ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term213 (x0 : nat) (x1 : nat -> Prop) := imp ((forall y0 : nat, (Peano.le x0 y0) -> x1 y0) /\ (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0)).
Definition term212 (x0 : nat) (x1 : nat -> Prop) := imp ((forall y0 : nat, (Peano.le x0 y0) -> x1 y0) /\ (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (Nat.add y0 (NUMERAL (BIT1 0))))) -> x1 y0)).
Definition term457 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term444 (x0 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> nat => forall y2 : nat, (Peano.lt y2 (y1 y2)) /\ (~ (x0 (y1 y2)))) y0.
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term68 (x0 : Prop) := (fun y0 : Prop => (~ y0) -> (x0 = y0) -> ~ x0) True.
Definition term486 (x0 : nat) (x1 : nat) := and ((Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)))).
Definition term301 (x0 : nat -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0.
Definition term269 (x0 : nat -> Prop) := exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1).
Definition term258 (x0 : nat -> Prop) := exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0).
Definition term407 (x0 : nat -> Prop) := or (forall y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (~ (x0 y1))).
Definition term514 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt x0 (S y1))) \/ ((x0 = y1) \/ (Peano.lt x0 y1))) y0.
Definition term509 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0.
Definition term24 (x0 : Prop) := @eq Prop (~ x0).
Definition term14 (x0 : Prop) (x1 : Prop) := ~ ((~ x0) /\ x1).
Definition term559 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.lt x2 x0)) \/ ((~ (x1 (S x2))) \/ (x1 x2)).
Definition term606 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term466 (x0 : nat -> nat) (x1 : nat -> Prop) := @eq Prop ((forall y0 : nat, (Peano.lt y0 (x0 y0)) /\ (~ (x1 (x0 y0)))) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x1 y1)) /\ (~ (x1 y0)))).
Definition term465 (x0 : nat -> nat) (x1 : nat -> Prop) := @eq Prop ((forall y0 : nat, (Peano.lt y0 (x0 y0)) /\ (~ (x1 (x0 y0)))) \/ (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x1 y2)) /\ (~ (x1 y1))) y0)).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term184 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ((forall y1 : a0, x0 y1) /\ (~ (x0 y0))) \/ ((~ (x0 y0)) /\ (forall y1 : a0, x0 y1)).
Definition term328 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term252 (x0 : nat -> Prop) (x1 : nat) := and ((fun y0 : nat => ~ (x0 y0)) x1).
Definition term547 := forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (S y1)) \/ (~ (y0 = y1))) /\ ((Peano.lt y0 (S y1)) \/ (~ (Peano.lt y0 y1))).
Definition term538 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term533 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1))).
Definition term492 := forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term478 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1).
Definition term359 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term324 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term317 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term329 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term456 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) := ((forall y0 : a0, x0 y0) /\ (exists y0 : a0, ~ (x0 y0))) \/ ((exists y0 : a0, ~ (x0 y0)) /\ (forall y0 : a0, x0 y0)).
Definition term18 := and (~ True).
Definition term379 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => (Peano.lt x0 y0) -> x1 y0) x2).
Definition term261 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (Peano.le y0 x0)) -> x1 y0.
Definition term527 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0) /\ ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) x0).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term111 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0, x0 y0).
Definition term383 (x0 : nat -> Prop) := ~ (ex x0).
Definition term300 (x0 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0.
Definition term26 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term19 (x0 : Prop) := (~ True) /\ x0.
Definition term199 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) /\ (x1 (Nat.add x2 (NUMERAL (BIT1 0)))).
Definition term398 (x0 : nat -> Prop) (x1 : nat) := ~ ((forall y0 : nat, (Peano.lt x1 y0) -> x0 y0) -> x0 x1).
Definition term206 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0.
Definition term205 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((Peano.lt y0 x0) /\ (x1 (Nat.add y0 (NUMERAL (BIT1 0))))) -> x1 y0.
Definition term36 (x0 : Prop) := (~ x0) -> True.
Definition term57 (x0 : Prop) := True /\ (~ x0).
Definition term350 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term588 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> Peano.lt x0 (S x1).
Definition term89 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x2 /\ x0) = x1) -> ~ x2.
Definition term132 (a0 : Type') (x0 : a0 -> Prop) := or ((forall y0 : a0, x0 y0) /\ (~ (~ (exists y0 : a0, ~ (x0 y0))))).
Definition term304 (x0 : nat -> Prop) := ~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0)).
Definition term610 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 (S x1))).
Definition term599 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2) \/ (~ (Peano.lt x1 x2))).
Definition term577 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term604 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ ((~ (x0 (S x1))) \/ (x0 x1))) -> ~ (Peano.lt x1 x2).
Definition term372 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ((~ (Peano.lt y0 x0)) \/ (~ (x1 (S y0)))) \/ (x1 y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term283 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term438 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term190 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term367 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := or (~ ((Peano.lt x2 x0) /\ (x1 (S x2)))).
Definition term65 (x0 : Prop) (x1 : Prop) := (~ x0) -> (x1 = x0) -> ~ x1.
Definition term139 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, x0 y1) /\ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term353 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term78 (x0 : Prop) := imp (x0 = False).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (exists y0 : a0, ~ (x0 y0)).
Definition term284 (x0 : nat -> Prop) := ~ (exists y0 : nat, (fun y1 : nat => (~ (x0 y1)) /\ (forall y2 : nat, (~ (Peano.le y2 y1)) -> x0 y2)) y0).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))).
Definition term70 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (~ y0) -> (x0 = y0) -> ~ x0) x1).
Definition term37 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) -> x0) = ((~ x0) -> y0)) x1).
Definition term13 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (~ ((~ y0) /\ x0)) = (x0 -> y0)) x1).
Definition term9 (x0 : Prop) := fun y0 : Prop => (~ ((~ y0) /\ x0)) = (x0 -> y0).
Definition term618 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term573 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le x1 (x0 x1))) -> Peano.le x1 (x0 x1).
Definition term388 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) y0).
Definition term104 (a0 : Type') := fun y0 : a0 -> Prop => (forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))).
Definition term482 (x0 : nat) (x1 : nat) := or (Peano.lt x0 (S x1)).
Definition term421 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => (Peano.lt y1 y2) /\ (~ (x0 y2))) x1 y0.
Definition term159 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((fun y0 : a0 => ~ (x1 y0)) x0) /\ (forall y0 : a0, x1 y0).
Definition term505 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1) /\ ((fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))) x1).
Definition term497 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term613 (x0 : nat -> Prop) (x1 : nat) := (x0 (S x1)) /\ (~ (x0 x1)).
Definition term80 (x0 : Prop) := (~ x0) -> ~ x0.
Definition term427 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (Peano.lt x2 (x1 x2)) /\ (~ (x0 (x1 x2))).
Definition term51 (x0 : Prop) (x1 : Prop) := (True /\ (~ x0)) -> ((x1 /\ True) = x0) -> ~ x1.
Definition term464 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x0 y2)) /\ (~ (x0 y1))) y0.
Definition term288 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (~ (x0 y1)) /\ (forall y2 : nat, (~ (Peano.le y2 y1)) -> x0 y2)) y0.
Definition term85 (x0 : Prop) (x1 : Prop) := ((x1 /\ False) = x0) -> ~ x1.
Definition term63 (x0 : Prop) (x1 : Prop) := ((x1 /\ True) = x0) -> ~ x1.
Definition term275 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) := (((~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False.
Definition term8 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term45 := imp (~ False).
Definition term105 (a0 : Type') := forall y0 : a0 -> Prop, (~ ((forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))))) -> False.
Definition term487 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1)))) /\ ((~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term397 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (~ (Peano.lt x1 y0)) \/ (x0 y0)) /\ (~ (x0 x1)).
Definition term396 (x0 : nat -> Prop) (x1 : nat) := (forall y0 : nat, (Peano.lt x1 y0) -> x0 y0) /\ (~ (x0 x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term16 (x0 : Prop) := (fun y0 : Prop => (~ ((~ y0) /\ x0)) = (x0 -> y0)) False.
Definition term198 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term451 (x0 : nat -> nat) (x1 : nat -> Prop) := ((fun y0 : nat -> nat => forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x1 (y0 y1)))) x0) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x1 y1)) /\ (~ (x1 y0))).
Definition term479 (x0 : nat) (x1 : nat) := ~ ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0.
Definition term556 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.lt x0 (S y0)) \/ (~ (x0 = y0))) /\ ((Peano.lt x0 (S y0)) \/ (~ (Peano.lt x0 y0)))) x1.
Definition term382 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (Peano.lt x0 y0) /\ (~ (x1 y0)).
Definition term308 (x0 : nat) (x1 : nat -> Prop) := (((forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False) -> (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False) -> ((forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False) -> (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term488 (x0 : nat) (x1 : nat) := ((Peano.lt x0 (S x1)) \/ ((~ (x0 = x1)) /\ (~ (Peano.lt x0 x1)))) /\ ((~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term585 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (x0 (x1 x2)) -> False.
Definition term295 (x0 : nat -> Prop) := forall y0 : nat, ~ ((~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1)).
Definition term517 (x0 : nat) := (forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ (forall y0 : nat, (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term211 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) /\ (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0).
Definition term210 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) /\ (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (Nat.add y0 (NUMERAL (BIT1 0))))) -> x1 y0).
Definition term218 (x0 : nat -> Prop) := fun y0 : nat => ((forall y1 : nat, (Peano.le y0 y1) -> x0 y1) /\ (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (S y1))) -> x0 y1)) -> forall y1 : nat, x0 y1.
Definition term217 (x0 : nat -> Prop) := fun y0 : nat => ((forall y1 : nat, (Peano.le y0 y1) -> x0 y1) /\ (forall y1 : nat, ((Peano.lt y1 y0) /\ (x0 (Nat.add y1 (NUMERAL (BIT1 0))))) -> x0 y1)) -> forall y1 : nat, x0 y1.
Definition term66 (x0 : Prop) := fun y0 : Prop => (~ y0) -> (x0 = y0) -> ~ x0.
Definition term244 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (~ (x0 y0)) -> Peano.le y0 x1.
Definition term54 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((x0 /\ (~ x1)) -> ((x2 /\ x0) = x1) -> ~ x2).
Definition term481 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 (S x1))) \/ ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term309 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term535 := and (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))).
Definition term543 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term566 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.lt x0 x1)) \/ (Peano.le x0 x1)).
Definition term58 (x0 : Prop) := imp (True /\ (~ x0)).
Definition term345 := forall y0 : nat -> Prop, forall y1 : nat, (forall y2 : nat, (Peano.le y1 y2) -> y0 y2) -> (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (S y2))) -> y0 y2) -> (~ ((exists y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) /\ (forall y2 : nat, (forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) -> y0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> ((forall y2 : nat, ~ (Peano.lt y2 (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 (S y3)) = ((y2 = y3) \/ (Peano.lt y2 y3)))) -> ~ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ (Peano.le y3 y2)).
Definition term344 := forall y0 : nat -> Prop, forall y1 : nat, (forall y2 : nat, (Peano.le y1 y2) -> y0 y2) -> (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (S y2))) -> y0 y2) -> (~ ((exists y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) /\ (forall y2 : nat, (forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) -> y0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> ((forall y2 : nat, (Peano.lt y2 (NUMERAL 0)) = False) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 (S y3)) = ((y2 = y3) \/ (Peano.lt y2 y3)))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ (Peano.le y3 y2)) -> False.
Definition term224 := forall y0 : nat -> Prop, forall y1 : nat, ((forall y2 : nat, (Peano.le y1 y2) -> y0 y2) /\ (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (S y2))) -> y0 y2)) -> forall y2 : nat, y0 y2.
Definition term223 := forall y0 : nat -> Prop, forall y1 : nat, ((forall y2 : nat, (Peano.le y1 y2) -> y0 y2) /\ (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (Nat.add y2 (NUMERAL (BIT1 0))))) -> y0 y2)) -> forall y2 : nat, y0 y2.
Definition term278 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt x0 y0) -> x1 y0.
Definition term225 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.le x0 y0) -> x1 y0.
Definition term511 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0))).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))))) -> False) x0.
Definition term84 (x0 : Prop) (x1 : Prop) := imp ((x0 /\ False) = x1).
Definition term61 (x0 : Prop) (x1 : Prop) := imp ((x0 /\ True) = x1).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or ((fun y0 : a0 => (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) x1).
Definition term516 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term385 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) y0).
Definition term285 (x0 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => (~ (x0 y1)) /\ (forall y2 : nat, (~ (Peano.le y2 y1)) -> x0 y2)) y0).
Definition term200 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) /\ (x1 (S x2)).
Definition term536 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0.
Definition term531 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term134 (a0 : Type') (x0 : a0 -> Prop) := ((forall y0 : a0, x0 y0) /\ (~ (~ (exists y0 : a0, ~ (x0 y0))))) \/ ((~ (forall y0 : a0, x0 y0)) /\ (~ (exists y0 : a0, ~ (x0 y0)))).
Definition term555 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt y0 (S y1)) \/ (~ (y0 = y1))) /\ ((Peano.lt y0 (S y1)) \/ (~ (Peano.lt y0 y1)))) x0.
Definition term553 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term549 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (Peano.le y0 y1)) x0.
Definition term526 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term524 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) x0.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => x0 y1) y0).
Definition term430 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (Peano.lt y1 y2) /\ (~ (x0 y2))) y0 (x1 y0).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) := (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False.
Definition term467 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (forall y0 : nat, (Peano.lt y0 (x0 y0)) /\ (~ (x1 (x0 y0)))) \/ ((fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x1 y1)) /\ (~ (x1 y0))) x2).
Definition term493 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)))).
Definition term319 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) \/ (exists y0 : a0, (~ (x0 y0)) /\ (forall y1 : a0, x0 y1)).
Definition term579 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term468 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat) := (forall y0 : nat, (Peano.lt y0 (x0 y0)) /\ (~ (x1 (x0 y0)))) \/ ((forall y0 : nat, (~ (Peano.lt x2 y0)) \/ (x1 y0)) /\ (~ (x1 x2))).
Definition term446 (x0 : nat -> Prop) := or (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (Peano.lt y2 (y1 y2)) /\ (~ (x0 (y1 y2)))) y0).
Definition term551 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 (x1 y0)) /\ (~ (x0 (x1 y0)))) x2.
Definition term449 (x0 : nat -> Prop) (x1 : nat -> nat) := or ((fun y0 : nat -> nat => forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1)))) x1).
Definition term483 (x0 : nat) (x1 : nat) := (Peano.lt x0 (S x1)) \/ (~ ((x0 = x1) \/ (Peano.lt x0 x1))).
Definition term204 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((Peano.lt x2 x0) /\ (x1 (S x2))) -> x1 x2.
Definition term474 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) \/ (Peano.le x0 x1).
Definition term311 := fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False.
Definition term168 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0) \/ ((fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0).
Definition term10 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ ((~ y0) /\ x0)) = (x0 -> y0)) x1.
Definition term384 (x0 : nat -> Prop) := ~ (exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1).
Definition term452 (x0 : nat -> nat) (x1 : nat -> Prop) := (forall y0 : nat, (Peano.lt y0 (x0 y0)) /\ (~ (x1 (x0 y0)))) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x1 y1)) /\ (~ (x1 y0))).
Definition term243 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => ~ (x0 y1)) y0) -> Peano.le y0 x1.
Definition term274 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 x1)).
Definition term504 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term426 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (fun y0 : nat => (Peano.lt x2 y0) /\ (~ (x0 y0))) (x1 x2).
Definition term408 (x0 : nat -> Prop) := (~ (exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1)) \/ (~ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0)).
Definition term409 (x0 : nat -> Prop) := (forall y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (~ (x0 y1))) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x0 y1)) /\ (~ (x0 y0))).
Definition term72 (x0 : Prop) := (fun y0 : Prop => (~ y0) -> (x0 = y0) -> ~ x0) False.
Definition term400 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) -> x0 y1) y0).
Definition term377 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt x0 y1) -> x1 y1) y0).
Definition term39 (x0 : Prop) (x1 : Prop) := @eq Prop (((~ x1) -> x0) = ((~ x0) -> x1)).
Definition term619 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x1 x0) \/ (Peano.le x0 x1)).
Definition term365 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((Peano.lt x2 x0) /\ (x1 (S x2))).
Definition term442 (x0 : nat -> Prop) := exists y0 : nat -> nat, ((fun y1 : nat -> nat => forall y2 : nat, (Peano.lt y2 (y1 y2)) /\ (~ (x0 (y1 y2)))) y0) \/ (exists y1 : nat, (forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (x0 y2)) /\ (~ (x0 y1))).
Definition term471 (x0 : nat -> nat) (x1 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (Peano.lt y1 (x0 y1)) /\ (~ (x1 (x0 y1)))) \/ ((forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x1 y1)) /\ (~ (x1 y0))).
Definition term67 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ y0) -> (x0 = y0) -> ~ x0) x1.
Definition term429 (x0 : nat -> Prop) (x1 : nat -> nat) := fun y0 : nat => (Peano.lt y0 (x1 y0)) /\ (~ (x0 (x1 y0))).
Definition term268 (x0 : nat -> Prop) := fun y0 : nat => (~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1).
Definition term257 (x0 : nat -> Prop) := fun y0 : nat => (~ (x0 y0)) /\ (forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0).
Definition term422 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) /\ (~ (x0 y3))) y0 y1.
Definition term50 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 /\ (~ x0)) -> ((x1 /\ y0) = x0) -> ~ x1) True.
Definition term534 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0).
Definition term512 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 (S y1)) \/ ((~ (x0 = y1)) /\ (~ (Peano.lt x0 y1)))) y0).
Definition term525 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) x0).
Definition term545 (x0 : nat) := forall y0 : nat, ((Peano.lt x0 (S y0)) \/ (~ (x0 = y0))) /\ ((Peano.lt x0 (S y0)) \/ (~ (Peano.lt x0 y0))).
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term489 (x0 : nat) := fun y0 : nat => ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term46 (x0 : Prop) := @eq Prop ((~ False) -> x0).
Definition term44 (x0 : Prop) := @eq Prop ((~ True) -> x0).
Definition term232 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => ~ (x0 y1)) y0.
Definition term615 (x0 : nat -> Prop) (x1 : nat) := imp ((x0 (S x1)) /\ (~ (x0 x1))).
Definition term183 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ((forall y1 : a0, x0 y1) /\ (~ (x0 y0))) \/ ((~ (x0 y0)) /\ (forall y1 : a0, x0 y1)).
Definition term626 (x0 : nat -> Prop) := (((exists y0 : nat, ~ (x0 y0)) /\ (exists y0 : nat, forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0)) = (exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0))) -> ~ (exists y0 : nat, ~ (x0 y0)).
Definition term55 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 /\ (~ x0)) -> ((x1 /\ y0) = x0) -> ~ x1) False.
Definition term33 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = ((~ x0) -> y0)) x1.
Definition term125 (a0 : Type') (x0 : a0 -> Prop) := and (~ (forall y0 : a0, x0 y0)).
Definition term564 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.lt x1 (x0 x1)).
Definition term197 (x0 : nat -> Prop) (x1 : nat) := x0 (S x1).
Definition term262 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (Peano.le y0 x0)) -> x1 y0.
Definition term360 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.le x0 x2) -> x1 x2.
Definition term21 := and (~ False).
Definition term94 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (x0 y1) -> Peano.le y1 y0).
Definition term88 (x0 : Prop) (x1 : Prop) := x0 /\ (~ x1).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((forall y0 : a0, x0 y0) /\ (exists y0 : a0, ~ (x0 y0))).
Definition term142 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((forall y0 : a0, x0 y0) /\ (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0)).
Definition term494 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term11 (x0 : Prop) := (fun y0 : Prop => (~ ((~ y0) /\ x0)) = (x0 -> y0)) True.
Definition term282 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term519 := forall y0 : nat, (forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ (forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term624 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (forall y2 : nat, (Peano.le y1 y2) -> y0 y2) -> (forall y2 : nat, ((Peano.lt y2 y1) /\ (y0 (S y2))) -> y0 y2) -> (~ ((exists y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) /\ (forall y2 : nat, (forall y3 : nat, (Peano.lt y2 y3) -> y0 y3) -> y0 y2))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) -> Peano.le y2 y3) -> ((forall y2 : nat, (Peano.lt y2 (NUMERAL 0)) = False) /\ (forall y2 : nat, forall y3 : nat, (Peano.lt y2 (S y3)) = ((y2 = y3) \/ (Peano.lt y2 y3)))) -> (forall y2 : nat, forall y3 : nat, (Peano.lt y2 y3) \/ (Peano.le y3 y2)) -> False) x0.
Definition term361 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.le x0 y0) -> x1 y0.
Definition term277 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt x0 y0) -> x1 y0.
Definition term440 (x0 : type1002) (x1 : Prop) := exists y0 : nat -> nat, (x0 y0) \/ x1.
Definition term503 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) x1).
Definition term403 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (forall y2 : nat, (Peano.lt y1 y2) -> x0 y2) -> x0 y1) y0).
Definition term380 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt x0 y1) -> x1 y1) y0).
Definition term293 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => (~ (x0 y1)) /\ (forall y2 : nat, (~ (Peano.le y2 y1)) -> x0 y2)) y0).
Definition term402 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0) x1).
Definition term291 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => (~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1)) x1).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, ~ (x0 y0)) /\ (forall y0 : a0, x0 y0)).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0) /\ (forall y0 : a0, x0 y0)).
Definition term69 (x0 : Prop) := (~ True) -> (x0 = True) -> ~ x0.
Definition term35 (x0 : Prop) := (~ True) -> x0.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) := (((~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> ((~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False.
Definition term355 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.le x0 x1.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term103 (a0 : Type') := fun y0 : a0 -> Prop => (~ ((forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))))) -> False.
Definition term242 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (x0 y0)) -> Peano.le y0 x1.
Definition term43 := imp (~ True).
Definition term22 (x0 : Prop) := (~ False) /\ x0.
Definition term431 (x0 : nat -> Prop) (x1 : nat -> nat) := forall y0 : nat, (Peano.lt y0 (x1 y0)) /\ (~ (x0 (x1 y0))).
Definition term194 := forall y0 : nat, (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term406 (x0 : nat -> Prop) := or (~ (exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1)).
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term357 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.le x0 y0.
Definition term303 (x0 : nat -> Prop) := (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0))) -> False.
Definition term191 := fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0)) x1.
Definition term96 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, ~ (x0 y0)).
Definition term476 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (Peano.le x0 y0).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term370 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((~ (Peano.lt x2 x0)) \/ (~ (x1 (S x2)))) \/ (x1 x2).
Definition term589 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term582 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (Peano.le x2 (x1 x2)) -> x0 (x1 x2).
Definition term378 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> x1 y0) x2.
Definition term7 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term154 (a0 : Type') (x0 : a0 -> Prop) := and (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term617 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> ~ (Peano.lt x0 x1).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (exists y0 : a0, ~ (x0 y0))).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => ~ (x0 y1)) y0) /\ (forall y1 : a0, x0 y1).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term302 (x0 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0).
Definition term75 (x0 : Prop) := (x0 = True) -> ~ x0.
Definition term593 (x0 : nat) := (x0 = x0) -> Peano.lt x0 (S x0).
Definition term537 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 (S y2))) \/ ((y1 = y2) \/ (Peano.lt y1 y2))) y0.
Definition term532 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 (S y2)) \/ ((~ (y1 = y2)) /\ (~ (Peano.lt y1 y2)))) y0.
Definition term602 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 (S x1))) -> x0 (S x1).
Definition term411 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term181 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((forall y0 : a0, x1 y0) /\ (~ (x1 x0))) \/ ((~ (x1 x0)) /\ (forall y0 : a0, x1 y0)).
Definition term334 (x0 : nat) (x1 : nat -> Prop) := (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term327 := imp (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1).
Definition term32 (x0 : Prop) := fun y0 : Prop => ((~ y0) -> x0) = ((~ x0) -> y0).
Definition term77 (x0 : Prop) := False -> x0 -> ~ x0.
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term166 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term307 (x0 : nat) (x1 : nat -> Prop) := (((forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False) -> (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False) -> (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term279 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> x0 y1.
Definition term263 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1.
Definition term368 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := or ((~ (Peano.lt x2 x0)) \/ (~ (x1 (S x2)))).
Definition term201 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := imp ((Peano.lt x2 x0) /\ (x1 (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, ~ (x0 y0)) /\ (forall y0 : a0, x0 y0).
Definition term234 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term592 (x0 : nat) (x1 : nat) := (x0 = x1) -> Peano.lt x0 (S x1).
Definition term458 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term332 (x0 : nat -> Prop) := (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x0 y1) -> x0 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term292 (x0 : nat) (x1 : nat -> Prop) := ~ ((~ (x1 x0)) /\ (forall y0 : nat, (~ (Peano.le y0 x0)) -> x1 y0)).
Definition term392 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (x1 y0).
Definition term363 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (x1 y0).
Definition term149 (a0 : Type') (x0 : a0 -> Prop) := or (exists y0 : a0, (forall y1 : a0, x0 y1) /\ (~ (x0 y0))).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) /\ (forall y1 : a0, x0 y1).
Definition term71 (x0 : Prop) (x1 : Prop) := @eq Prop ((~ x0) -> (x1 = x0) -> ~ x1).
Definition term616 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((x0 (S x1)) /\ (~ (x0 x1))) -> ~ (Peano.lt x1 x2).
Definition term34 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> x0) = ((~ x0) -> y0)) True.
Definition term271 (x0 : nat -> Prop) := ~ (exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (Peano.le y1 y0)) -> x0 y1)).
Definition term270 (x0 : nat -> Prop) := ~ (exists y0 : nat, (~ (x0 y0)) /\ (forall y1 : nat, (~ (x0 y1)) -> Peano.le y1 y0)).
Definition term254 (x0 : nat -> Prop) (x1 : nat) := ((fun y0 : nat => ~ (x0 y0)) x1) /\ (forall y0 : nat, ((fun y1 : nat => ~ (x0 y1)) y0) -> Peano.le y0 x1).
Definition term214 (x0 : nat -> Prop) := forall y0 : nat, x0 y0.
Definition term546 := fun y0 : nat => forall y1 : nat, ((Peano.lt y0 (S y1)) \/ (~ (y0 = y1))) /\ ((Peano.lt y0 (S y1)) \/ (~ (Peano.lt y0 y1))).
Definition term523 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term522 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1))).
Definition term491 := fun y0 : nat => forall y1 : nat, ((Peano.lt y0 (S y1)) \/ ((~ (y0 = y1)) /\ (~ (Peano.lt y0 y1)))) /\ ((~ (Peano.lt y0 (S y1))) \/ ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term354 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term306 (x0 : nat) (x1 : nat -> Prop) := ((forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False) -> (forall y0 : nat, (Peano.le x0 y0) -> x1 y0) -> (forall y0 : nat, ((Peano.lt y0 x0) /\ (x1 (S y0))) -> x1 y0) -> (~ ((exists y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y0 y1) -> x1 y1) -> x1 y0))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)))) -> (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term608 (x0 : nat -> Prop) (x1 : nat) := ~ ((~ (x0 (S x1))) \/ (x0 x1)).
Definition term584 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (~ (x0 (x1 x2))) -> x0 (x1 x2).
Definition term490 (x0 : nat) := forall y0 : nat, ((Peano.lt x0 (S y0)) \/ ((~ (x0 = y0)) /\ (~ (Peano.lt x0 y0)))) /\ ((~ (Peano.lt x0 (S y0))) \/ ((x0 = y0) \/ (Peano.lt x0 y0))).
Definition term450 (x0 : nat -> Prop) (x1 : nat -> nat) := or (forall y0 : nat, (Peano.lt y0 (x1 y0)) /\ (~ (x0 (x1 y0)))).
Definition term76 (x0 : Prop) := x0 -> ~ x0.
Definition term229 (x0 : nat -> Prop) := fun y0 : nat => ~ (x0 y0).
Definition term48 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (y0 /\ (~ x0)) -> ((x1 /\ y0) = x0) -> ~ x1.
Definition term346 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ (Peano.le x0 x1).
Definition term52 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (y0 /\ (~ x0)) -> ((x1 /\ y0) = x0) -> ~ x1) x2).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => x0 y0) x1).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, x0 y1) /\ (~ (x0 y0)).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0) /\ (forall y0 : a0, x0 y0).
Definition term590 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term580 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
Definition term570 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.lt x0 x1))).
Definition term448 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat -> nat, forall y1 : nat, (Peano.lt y1 (y0 y1)) /\ (~ (x0 (y0 y1)))) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x0 y1)) /\ (~ (x0 y0)))).
Definition term447 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (Peano.lt y2 (y1 y2)) /\ (~ (x0 (y1 y2)))) y0) \/ (exists y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (x0 y1)) /\ (~ (x0 y0)))).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) \/ (exists y0 : a0, (~ (x0 y0)) /\ (forall y1 : a0, x0 y1))).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0) \/ (exists y0 : a0, (fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0)).
