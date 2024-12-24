Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := imp ((x1 = x0) \/ (@IN nat x1 x2)).
Definition term8 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term379 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term432 (x0 : nat -> Prop) := (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> ~ (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0).
Definition term187 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (~ (exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0)).
Definition term117 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := forall y0 : nat, ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2.
Definition term116 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := forall y0 : nat, (@IN nat y0 (@INSERT nat x0 x1)) -> Peano.le y0 x2.
Definition term390 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))))).
Definition term200 (x0 : nat) := (fun y0 : nat => forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2) x0.
Definition term424 (x0 : nat -> Prop) := (((~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False) -> (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False) -> (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False.
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2)).
Definition term90 := fun y0 : nat -> Prop => (@FINITE nat y0) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0.
Definition term437 (x0 : nat -> Prop) (x1 : nat -> Prop) := ((@FINITE nat x0) /\ (@SUBSET nat x1 x0)) -> @FINITE nat x1.
Definition term357 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.le x1 x0) /\ (~ (Peano.le x1 x2))).
Definition term518 (x0 : nat -> Prop) (x1 : nat -> Prop) := ~ ((~ (@FINITE nat x1)) \/ (~ (@SUBSET nat x0 x1))).
Definition term190 (x0 : type993) := ~ (all x0).
Definition term167 (x0 : nat -> Prop) := ~ (all x0).
Definition term416 := (~ False) -> False.
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat -> nat) := ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ ((fun y0 : nat -> nat => forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))) x3).
Definition term468 (x0 : nat -> Prop) (x1 : nat -> Prop) := or ((~ (@FINITE nat x1)) \/ (~ (@SUBSET nat x0 x1))).
Definition term146 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term259 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) x2).
Definition term356 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2))).
Definition term112 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := (@IN nat x2 (@INSERT nat x0 x1)) -> Peano.le x2 x3.
Definition term196 (x0 : nat) := fun y0 : nat -> Prop => ~ ((fun y1 : nat -> Prop => ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat x0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = x0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2) y0).
Definition term94 := ((exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0) /\ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2)) -> forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1.
Definition term290 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.le x1 x2))).
Definition term502 (x0 : nat -> Prop) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => ((~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))) \/ (@FINITE nat x0)) x1.
Definition term405 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (~ (@IN nat (x0 x1) x2)) -> @IN nat (x0 x1) x2.
Definition term42 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL 0) x0) /\ (Peano.le x0 x1).
Definition term400 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ ((x0 x1) = x2).
Definition term436 := forall y0 : nat -> Prop, (~ ((exists y1 : nat, @SUBSET nat y0 (dotdot (NUMERAL 0) y1)) -> @FINITE nat y0)) -> (forall y1 : nat, forall y2 : nat, @FINITE nat (dotdot y1 y2)) -> ~ (forall y1 : nat -> Prop, forall y2 : nat -> Prop, ((@FINITE nat y2) /\ (@SUBSET nat y1 y2)) -> @FINITE nat y1).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1))) x1.
Definition term162 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0).
Definition term120 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0.
Definition term74 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (@IN nat y1 (@INSERT nat x0 x1)) -> Peano.le y1 y0.
Definition term62 := exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0.
Definition term54 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term418 (x0 : nat -> Prop) := (exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0.
Definition term100 (x0 : nat) := forall y0 : nat, (@IN nat y0 (@EMPTY nat)) -> Peano.le y0 x0.
Definition term49 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1.
Definition term351 (x0 : Prop) := ~ (~ x0).
Definition term252 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0) /\ (exists y1 : nat -> nat, forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term300 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2)) x0.
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term336 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 x1) x1.
Definition term521 (x0 : nat -> Prop) := and (~ (~ (@FINITE nat x0))).
Definition term467 (x0 : nat -> Prop) (x1 : nat -> Prop) := or (~ ((@FINITE nat x1) /\ (@SUBSET nat x0 x1))).
Definition term144 := (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term163 (x0 : nat -> Prop) := and (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)).
Definition term67 (x0 : nat -> Prop) := and (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0).
Definition term64 := and (exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0).
Definition term193 (x0 : nat) := exists y0 : nat -> Prop, ~ ((fun y1 : nat -> Prop => ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat x0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = x0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2) y0).
Definition term48 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (@IN nat y0 x0) -> @IN nat y0 (dotdot (NUMERAL 0) x1).
Definition term229 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y0 y1.
Definition term227 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term184 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, exists y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0)).
Definition term219 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 y0)) x0) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2)).
Definition term308 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2)).
Definition term439 (x0 : nat -> Prop) := forall y0 : nat -> Prop, ((@FINITE nat y0) /\ (@SUBSET nat x0 y0)) -> @FINITE nat x0.
Definition term53 (x0 : nat -> Prop) := exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0).
Definition term457 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) /\ (~ (@FINITE nat x0))).
Definition term456 (x0 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y1)) y0) /\ (~ (@FINITE nat x0))).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term192 (x0 : nat) := ~ (forall y0 : nat -> Prop, ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1).
Definition term102 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term530 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (~ ((exists y1 : nat, @SUBSET nat y0 (dotdot (NUMERAL 0) y1)) -> @FINITE nat y0)) -> (forall y1 : nat, forall y2 : nat, @FINITE nat (dotdot y1 y2)) -> (forall y1 : nat -> Prop, forall y2 : nat -> Prop, ((@FINITE nat y2) /\ (@SUBSET nat y1 y2)) -> @FINITE nat y1) -> False) x0.
Definition term329 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 (x0 x1)) (x0 x1))) -> Peano.le (x0 x1) (x0 (x0 x1)).
Definition term142 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term511 (x0 : nat -> Prop) (x1 : nat -> Prop) := (@FINITE nat x0) \/ (~ (@SUBSET nat x0 x1)).
Definition term38 (x0 : nat -> Prop) (x1 : nat) := @SUBSET nat x0 (dotdot (NUMERAL 0) x1).
Definition term355 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) /\ (~ (Peano.le x1 x2)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term407 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (Peano.le x1 x0) \/ (~ (@IN nat x1 x2)).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term267 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term127 (x0 : Prop) := (~ x0) -> False.
Definition term171 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2) x3.
Definition term51 (x0 : nat -> Prop) := fun y0 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y0).
Definition term524 (x0 : nat -> Prop) (x1 : nat -> Prop) := imp (~ ((~ (@FINITE nat x1)) \/ (~ (@SUBSET nat x0 x1)))).
Definition term295 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term380 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term149 := fun y0 : nat => Peano.le y0 y0.
Definition term344 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2)).
Definition term401 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((x0 x1) = x2) -> ~ ((x0 x1) = x2).
Definition term250 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term507 (x0 : nat) := ~ (@FINITE nat (dotdot (NUMERAL 0) x0)).
Definition term403 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat -> Prop) := @eq Prop (((x1 x2) = x0) \/ (@IN nat (x1 x2) x3)).
Definition term268 (x0 : Prop) (x1 : type1002) := x0 /\ (exists y0 : nat -> nat, x1 y0).
Definition term305 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term438 (x0 : nat -> Prop) := fun y0 : nat -> Prop => ((@FINITE nat y0) /\ (@SUBSET nat x0 y0)) -> @FINITE nat x0.
Definition term484 (x0 : nat -> Prop) (x1 : nat -> Prop) := or ((fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))) x1).
Definition term327 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term236 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => ((y2 = x0) \/ (@IN nat y2 x1)) /\ (~ (Peano.le y2 y1))) x2 y0.
Definition term384 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term95 (x0 : nat) := imp (@IN nat x0 (@EMPTY nat)).
Definition term137 := imp (forall y0 : nat, Peano.le y0 y0).
Definition term113 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ((x2 = x0) \/ (@IN nat x2 x1)) -> Peano.le x2 x3.
Definition term489 (x0 : nat -> Prop) := fun y0 : nat -> Prop => (fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat x0 y1))) y0.
Definition term169 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ (forall y0 : nat, ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2).
Definition term135 := ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term129 := ~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2).
Definition term10 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2))) x0.
Definition term244 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := fun y0 : nat => (((x2 y0) = x0) \/ (@IN nat (x2 y0) x1)) /\ (~ (Peano.le (x2 y0) y0)).
Definition term285 (x0 : nat) := exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat -> nat, ((forall y3 : nat, (~ (@IN nat y3 y0)) \/ (Peano.le y3 y1)) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) /\ (forall y3 : nat, (((y2 y3) = x0) \/ (@IN nat (y2 y3) y0)) /\ (~ (Peano.le (y2 y3) y3))).
Definition term186 (x0 : nat) (x1 : nat -> Prop) := and ((exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term185 (x0 : nat) (x1 : nat -> Prop) := and ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term266 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term24 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term395 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (((x1 (x1 x0)) = x2) /\ ((~ (Peano.le (x1 x2) x2)) /\ (Peano.le (x1 (x1 x0)) (x1 (x1 x0))))) -> ~ ((x1 (x1 x0)) = (x1 x2)).
Definition term461 (x0 : nat) (x1 : nat -> Prop) := (@SUBSET nat x1 (dotdot (NUMERAL 0) x0)) /\ (~ (@FINITE nat x1)).
Definition term470 (x0 : nat -> Prop) (x1 : nat -> Prop) := ((~ (@FINITE nat x0)) \/ (~ (@SUBSET nat x1 x0))) \/ (@FINITE nat x1).
Definition term307 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1)) x2.
Definition term195 (x0 : nat) (x1 : nat -> Prop) := ~ ((fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1) x1).
Definition term427 := ~ (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0).
Definition term388 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x1)) /\ (Peano.le x2 x3).
Definition term334 (x0 : Prop) := (~ x0) -> x0.
Definition term419 (x0 : nat -> Prop) := (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> False.
Definition term75 (x0 : nat) (x1 : nat -> Prop) := (((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x1) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) -> (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@INSERT nat x0 x1).
Definition term451 (x0 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y1)) y0) /\ (~ (@FINITE nat x0)).
Definition term221 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := imp (@IN nat x0 (@INSERT nat x1 x2)).
Definition term69 (x0 : nat) (x1 : nat -> Prop) := ((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x1) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term348 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term331 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 x1) (x0 (x0 x1)).
Definition term510 (x0 : nat -> Prop) (x1 : nat -> Prop) := (~ (@SUBSET nat x1 x0)) \/ (@FINITE nat x1).
Definition term183 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => exists y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0)).
Definition term225 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term375 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 (x0 x1)) (x0 (x0 x1)).
Definition term342 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2))).
Definition term455 (x0 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y1)) y0).
Definition term256 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0).
Definition term214 (x0 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0).
Definition term141 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term443 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term506 (x0 : nat) := (~ (@FINITE nat (dotdot (NUMERAL 0) x0))) -> @FINITE nat (dotdot (NUMERAL 0) x0).
Definition term446 (x0 : nat -> Prop) := imp (exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)).
Definition term391 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x3 = x1) /\ ((~ (Peano.le x0 x1)) /\ (Peano.le x2 x3))).
Definition term343 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term249 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1)).
Definition term230 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y1 (y0 y1).
Definition term228 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term435 := forall y0 : nat -> Prop, (~ ((exists y1 : nat, @SUBSET nat y0 (dotdot (NUMERAL 0) y1)) -> @FINITE nat y0)) -> (forall y1 : nat, forall y2 : nat, @FINITE nat (dotdot y1 y2)) -> (forall y1 : nat -> Prop, forall y2 : nat -> Prop, ((@FINITE nat y2) /\ (@SUBSET nat y1 y2)) -> @FINITE nat y1) -> False.
Definition term381 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x3 = x1))) /\ (~ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term394 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ((x1 (x1 x2)) = x0) /\ ((~ (Peano.le (x1 x0) x0)) /\ (Peano.le (x1 (x1 x2)) (x1 (x1 x2)))).
Definition term519 (x0 : nat -> Prop) (x1 : nat -> Prop) := (~ (~ (@FINITE nat x1))) /\ (~ (~ (@SUBSET nat x0 x1))).
Definition term358 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) /\ (~ (Peano.le x0 x2))) -> ~ (Peano.le x1 x2).
Definition term337 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.le x1 x2).
Definition term335 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 x1) x1) -> ~ (Peano.le (x0 x1) x1).
Definition term453 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y1)) y0.
Definition term429 := (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False.
Definition term477 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term374 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ ((x0 (x0 x1)) = x2).
Definition term517 (x0 : nat -> Prop) (x1 : nat -> Prop) := (~ ((~ (@FINITE nat x0)) \/ (~ (@SUBSET nat x1 x0)))) -> @FINITE nat x1.
Definition term459 (x0 : nat -> Prop) (x1 : nat) := and (@SUBSET nat x0 (dotdot (NUMERAL 0) x1)).
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat -> nat) := ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (forall y0 : nat, (((x3 y0) = x1) \/ (@IN nat (x3 y0) x2)) /\ (~ (Peano.le (x3 y0) y0))).
Definition term396 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ~ ((x1 (x1 x0)) = (x1 x2)).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term105 := exists y0 : nat, True.
Definition term301 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1)) x1.
Definition term211 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) x1.
Definition term28 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term328 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> Peano.le x0 x1.
Definition term281 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat -> nat, ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term198 (x0 : nat) := exists y0 : nat -> Prop, ((exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) /\ (forall y1 : nat, exists y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) /\ (~ (Peano.le y2 y1))).
Definition term86 := (exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0) /\ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2).
Definition term43 (x0 : nat) := and (Peano.le (NUMERAL 0) x0).
Definition term500 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x1 = x0) \/ (@IN nat x1 x2).
Definition term269 (x0 : Prop) (x1 : type1002) := exists y0 : nat -> nat, x0 /\ (x1 y0).
Definition term495 := fun y0 : nat -> Prop => (forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat y0 y1))) \/ (@FINITE nat y0).
Definition term296 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term161 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0).
Definition term154 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term148 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term119 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0.
Definition term118 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (@IN nat y1 (@INSERT nat x0 x1)) -> Peano.le y1 y0.
Definition term104 := fun y0 : nat => forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0.
Definition term52 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term385 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term147 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term61 := (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat).
Definition term480 (x0 : nat -> Prop) := forall y0 : nat -> Prop, ((fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat x0 y1))) y0) \/ (@FINITE nat x0).
Definition term210 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat -> nat => ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ ((fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x1) \/ (@IN nat (y1 y2) x2)) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term463 (x0 : nat -> Prop) := fun y0 : nat => (@SUBSET nat x0 (dotdot (NUMERAL 0) y0)) /\ (~ (@FINITE nat x0)).
Definition term124 := fun y0 : nat => forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2.
Definition term82 := fun y0 : nat => forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2.
Definition term66 (x0 : nat -> Prop) := and ((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x0).
Definition term447 (x0 : nat -> Prop) := ~ (@FINITE nat x0).
Definition term165 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ~ (((x2 = x0) \/ (@IN nat x2 x1)) -> Peano.le x2 x3).
Definition term474 := fun y0 : nat -> Prop => forall y1 : nat -> Prop, ((~ (@FINITE nat y1)) \/ (~ (@SUBSET nat y0 y1))) \/ (@FINITE nat y0).
Definition term440 := fun y0 : nat -> Prop => forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0.
Definition term527 (x0 : nat) (x1 : nat -> Prop) := ((@FINITE nat (dotdot (NUMERAL 0) x0)) /\ (@SUBSET nat x1 (dotdot (NUMERAL 0) x0))) -> @FINITE nat x1.
Definition term503 (x0 : nat -> Prop) (x1 : nat -> Prop) := (~ (@FINITE nat x0)) \/ ((~ (@SUBSET nat x1 x0)) \/ (@FINITE nat x1)).
Definition term367 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := ~ (@IN nat (x0 (x0 x1)) x2).
Definition term59 := (((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat)) /\ (forall y0 : nat, forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1))) -> forall y0 : nat -> Prop, (@FINITE nat y0) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0.
Definition term406 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := ~ (@IN nat (x0 x1) x2).
Definition term303 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term121 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) -> exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0.
Definition term76 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) -> exists y0 : nat, forall y1 : nat, (@IN nat y1 (@INSERT nat x0 x1)) -> Peano.le y1 y0.
Definition term309 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term294 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term258 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1)))).
Definition term257 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1)))).
Definition term115 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2.
Definition term426 := (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False.
Definition term134 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term92 := forall y0 : nat -> Prop, (@FINITE nat y0) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0.
Definition term47 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) -> Peano.le x1 x2.
Definition term469 (x0 : nat -> Prop) (x1 : nat -> Prop) := (~ ((@FINITE nat x0) /\ (@SUBSET nat x1 x0))) \/ (@FINITE nat x1).
Definition term248 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1)).
Definition term247 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y1 (y0 y1).
Definition term274 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))) y0.
Definition term160 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1).
Definition term361 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 (x0 x1)) x1).
Definition term239 (x0 : nat) (x1 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))).
Definition term238 (x0 : nat) (x1 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y0 y1).
Definition term133 := (((~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term402 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (@IN nat (x1 x2) x0) \/ ((x1 x2) = x3).
Definition term218 (x0 : nat -> Prop) (x1 : nat) := and (forall y0 : nat, (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1)).
Definition term126 := True /\ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2).
Definition term433 := fun y0 : nat -> Prop => (~ ((exists y1 : nat, @SUBSET nat y0 (dotdot (NUMERAL 0) y1)) -> @FINITE nat y0)) -> (forall y1 : nat, forall y2 : nat, @FINITE nat (dotdot y1 y2)) -> (forall y1 : nat -> Prop, forall y2 : nat -> Prop, ((@FINITE nat y2) /\ (@SUBSET nat y1 y2)) -> @FINITE nat y1) -> False.
Definition term93 := forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1.
Definition term107 (x0 : Prop) := exists y0 : nat, x0.
Definition term131 := ((~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term365 (x0 : nat) (x1 : nat -> Prop) := ~ (@IN nat x0 x1).
Definition term532 := forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, @SUBSET nat y0 (dotdot (NUMERAL 0) y1)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term317 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term313 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x2 x3) = (Peano.le x0 x1)) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term404 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat -> Prop) := (~ ((x1 x2) = x0)) -> @IN nat (x1 x2) x3.
Definition term333 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 x1) (x0 (x0 x1))).
Definition term471 (x0 : nat -> Prop) (x1 : nat -> Prop) := (@FINITE nat x1) /\ (@SUBSET nat x0 x1).
Definition term377 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 (x0 x1)) (x0 (x0 x1))).
Definition term241 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) /\ (~ (Peano.le y0 x3))) (x2 x3).
Definition term292 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term273 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))) y0.
Definition term452 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) x1.
Definition term50 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (@IN nat y0 x0) -> Peano.le y0 x1.
Definition term37 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) -> @IN nat y0 x1.
Definition term91 := fun y0 : nat -> Prop => (@FINITE nat y0) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1.
Definition term490 (x0 : nat -> Prop) := forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat x0 y1))) y0.
Definition term449 (x0 : nat -> Prop) := (exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) /\ (~ (@FINITE nat x0)).
Definition term347 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term445 := forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1).
Definition term299 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term297 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term157 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term155 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term136 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term125 := forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2.
Definition term84 := forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2.
Definition term83 := forall y0 : nat, forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1).
Definition term27 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term265 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (exists y1 : nat -> nat, forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term56 (x0 : nat -> Prop) := (@FINITE nat x0) -> exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0).
Definition term272 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1))) x2.
Definition term513 (x0 : nat -> Prop) (x1 : nat -> Prop) := (~ (@FINITE nat x1)) \/ ((@FINITE nat x0) \/ (~ (@SUBSET nat x0 x1))).
Definition term464 (x0 : nat -> Prop) := exists y0 : nat, (@SUBSET nat x0 (dotdot (NUMERAL 0) y0)) /\ (~ (@FINITE nat x0)).
Definition term398 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ ((x0 x1) = (x0 x2))) -> ~ (x1 = x2).
Definition term73 (x0 : nat) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@INSERT nat x0 x1).
Definition term206 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term460 (x0 : nat) (x1 : nat -> Prop) := ((fun y0 : nat => @SUBSET nat x1 (dotdot (NUMERAL 0) y0)) x0) /\ (~ (@FINITE nat x1)).
Definition term479 (x0 : type993) (x1 : Prop) := (forall y0 : nat -> Prop, x0 y0) \/ x1.
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) x0) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term512 (x0 : nat -> Prop) := or (~ (@FINITE nat x0)).
Definition term251 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term176 (x0 : nat -> Prop) := ~ (ex x0).
Definition term420 (x0 : nat -> Prop) := ~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0).
Definition term528 (x0 : nat -> Prop) := (~ (@FINITE nat x0)) -> @FINITE nat x0.
Definition term498 (x0 : nat -> Prop) := @eq Prop ((forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))) \/ (@FINITE nat x0)).
Definition term497 (x0 : nat -> Prop) := @eq Prop ((forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat x0 y1))) y0) \/ (@FINITE nat x0)).
Definition term180 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0) x2.
Definition term369 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat (x0 (x0 x1)) x2.
Definition term423 (x0 : nat -> Prop) := ((~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False) -> (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False.
Definition term132 := (((~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term482 (x0 : nat -> Prop) := fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0)).
Definition term231 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0)).
Definition term444 := fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat x0 (@INSERT nat x1 x2).
Definition term139 := (forall y0 : nat, Peano.le y0 y0) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term465 (x0 : nat -> Prop) (x1 : nat -> Prop) := ~ ((@FINITE nat x1) /\ (@SUBSET nat x0 x1)).
Definition term494 (x0 : nat -> Prop) := (forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))) \/ (@FINITE nat x0).
Definition term472 (x0 : nat -> Prop) := fun y0 : nat -> Prop => ((~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))) \/ (@FINITE nat x0).
Definition term101 := forall y0 : nat, True.
Definition term282 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => exists y1 : nat -> nat, ((forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term203 := fun y0 : nat => exists y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2)) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) /\ (forall y2 : nat, exists y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) /\ (~ (Peano.le y3 y2))).
Definition term232 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))) x2.
Definition term366 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (~ (Peano.le (x0 (x0 x1)) x1)) -> ~ (@IN nat (x0 (x0 x1)) x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term177 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term164 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term70 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term138 := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term45 (x0 : nat) (x1 : nat -> Prop) := imp (@IN nat x0 x1).
Definition term414 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 x1) x1)) -> Peano.le (x0 x1) x1.
Definition term368 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (@IN nat (x0 (x0 x1)) x2) -> ~ (@IN nat (x0 (x0 x1)) x2).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) = (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1)) x0.
Definition term318 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term25 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term245 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => ((y2 = x0) \/ (@IN nat y2 x1)) /\ (~ (Peano.le y2 y1))) y0 (x2 y0).
Definition term58 (x0 : type993) := ((x0 (@EMPTY nat)) /\ (forall y0 : nat, forall y1 : nat -> Prop, ((x0 y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> x0 (@INSERT nat y0 y1))) -> forall y0 : nat -> Prop, (@FINITE nat y0) -> x0 y0.
Definition term19 (a0 : Type') (x0 : type686 a0) := ((x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term99 := fun y0 : nat => True.
Definition term29 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term411 (x0 : nat) (x1 : nat -> Prop) := ~ (~ (@IN nat x0 x1)).
Definition term40 (x0 : nat) := dotdot (NUMERAL 0) x0.
Definition term360 (x0 : nat -> nat) (x1 : nat) := ((Peano.le (x0 x1) (x0 (x0 x1))) /\ (~ (Peano.le (x0 x1) x1))) -> ~ (Peano.le (x0 (x0 x1)) x1).
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop (((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1)))).
Definition term275 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop (((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x1) \/ (@IN nat (y1 y2) x2)) /\ (~ (Peano.le (y1 y2) y2))) y0)).
Definition term291 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term172 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ~ ((fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2) x3).
Definition term208 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term493 (x0 : nat -> Prop) := or (forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))).
Definition term128 := (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> False.
Definition term71 (x0 : nat) (x1 : nat -> Prop) := imp (((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x1) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term202 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat -> Prop, ((exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) /\ ((~ (@IN nat y1 y2)) /\ (@FINITE nat y2))) -> exists y3 : nat, forall y4 : nat, ((y4 = y1) \/ (@IN nat y4 y2)) -> Peano.le y4 y3) y0).
Definition term182 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 x1)) -> Peano.le y2 y1) y0).
Definition term145 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term315 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term79 (x0 : nat) := forall y0 : nat -> Prop, (((fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) (@INSERT nat x0 y0).
Definition term483 (x0 : nat -> Prop) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))) x1.
Definition term508 (x0 : nat -> Prop) (x1 : nat) := (~ (@SUBSET nat x0 (dotdot (NUMERAL 0) x1))) -> @SUBSET nat x0 (dotdot (NUMERAL 0) x1).
Definition term85 := ((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat)) /\ (forall y0 : nat, forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1)).
Definition term130 := (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term476 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term488 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat -> Prop, ((~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))) \/ (@FINITE nat x0)).
Definition term487 (x0 : nat -> Prop) := @eq Prop (forall y0 : nat -> Prop, ((fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat x0 y1))) y0) \/ (@FINITE nat x0)).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0))) x2.
Definition term98 (x0 : nat) := fun y0 : nat => (@IN nat y0 (@EMPTY nat)) -> Peano.le y0 x0.
Definition term529 (x0 : nat -> Prop) := (@FINITE nat x0) -> False.
Definition term454 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y1)) y0.
Definition term255 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0.
Definition term189 (x0 : nat) (x1 : nat -> Prop) := ~ (((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) -> exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0).
Definition term413 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (@IN nat (x1 x2) x0) -> Peano.le (x1 x2) x2.
Definition term425 (x0 : nat -> Prop) := (((~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False) -> (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False) -> ((~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False) -> (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False.
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term373 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ ((x0 (x0 x1)) = x2)) -> (x0 (x0 x1)) = x2.
Definition term330 (x0 : nat -> nat) (x1 : nat) := x0 (x0 x1).
Definition term217 (x0 : nat -> Prop) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) x1).
Definition term383 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term353 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term106 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term350 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x0))) /\ (~ (Peano.le x1 x2)).
Definition term17 (a0 : Type') := forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term153 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term339 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term363 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 (x0 x1)) x1.
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term349 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2)).
Definition term462 (x0 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y1)) y0) /\ (~ (@FINITE nat x0)).
Definition term235 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => ((y2 = x0) \/ (@IN nat y2 x1)) /\ (~ (Peano.le y2 y1))) x2 y0.
Definition term392 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = x0) /\ ((~ (Peano.le x3 x0)) /\ (Peano.le x2 x1))) -> ~ (x2 = x3).
Definition term345 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.le x0 x1)) \/ (Peano.le x0 x2))) -> ~ (Peano.le x1 x2).
Definition term332 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 x1) (x0 (x0 x1)))) -> Peano.le (x0 x1) (x0 (x0 x1)).
Definition term466 (x0 : nat -> Prop) (x1 : nat -> Prop) := (~ (@FINITE nat x1)) \/ (~ (@SUBSET nat x0 x1)).
Definition term242 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) (x3 : nat) := (((x2 x3) = x0) \/ (@IN nat (x2 x3) x1)) /\ (~ (Peano.le (x2 x3) x3)).
Definition term314 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term233 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))) x2 x3.
Definition term123 (x0 : nat) := forall y0 : nat -> Prop, ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1.
Definition term80 (x0 : nat) := forall y0 : nat -> Prop, ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 (@INSERT nat x0 y0)) -> Peano.le y2 y1.
Definition term312 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term441 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term216 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term215 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term324 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 (x0 x1)) (x0 x1).
Definition term284 (x0 : nat) := fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat -> nat, ((forall y3 : nat, (~ (@IN nat y3 y0)) \/ (Peano.le y3 y1)) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) /\ (forall y3 : nat, (((y2 y3) = x0) \/ (@IN nat (y2 y3) y0)) /\ (~ (Peano.le (y2 y3) y3))).
Definition term60 := fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1.
Definition term201 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2) x0).
Definition term311 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 x1) x1).
Definition term77 (x0 : nat) := fun y0 : nat -> Prop => (((fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) (@INSERT nat x0 y0).
Definition term504 (x0 : nat -> Prop) (x1 : nat -> Prop) := ~ (@SUBSET nat x0 x1).
Definition term475 := forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((~ (@FINITE nat y1)) \/ (~ (@SUBSET nat y0 y1))) \/ (@FINITE nat y0).
Definition term421 := forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0.
Definition term207 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term18 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) x0.
Definition term450 (x0 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y1)) y0) /\ (~ (@FINITE nat x0)).
Definition term179 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 x1)) -> Peano.le y2 y1) y0).
Definition term378 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x1 = x0)) \/ ((Peano.le x3 x0) \/ (~ (Peano.le x2 x1))))) -> ~ (x2 = x3).
Definition term212 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0.
Definition term88 := imp ((exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0) /\ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2)).
Definition term408 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((~ (@IN nat x1 x0)) \/ (Peano.le x1 x2)).
Definition term304 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term114 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => (@IN nat y0 (@INSERT nat x0 x1)) -> Peano.le y0 x2.
Definition term341 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term253 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) x2.
Definition term352 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term323 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 (x0 x1)) (x0 x1)) -> ~ (Peano.le (x0 (x0 x1)) (x0 x1)).
Definition term409 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((Peano.le x1 x0) \/ (~ (@IN nat x1 x2))).
Definition term246 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := forall y0 : nat, (((x2 y0) = x0) \/ (@IN nat (x2 y0) x1)) /\ (~ (Peano.le (x2 y0) y0)).
Definition term322 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 (x0 x1)) (x0 x1)).
Definition term448 (x0 : nat -> Prop) := and (exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)).
Definition term224 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term21 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term492 (x0 : nat -> Prop) := or (forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat x0 y1))) y0).
Definition term293 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term72 (x0 : nat) (x1 : nat -> Prop) := imp ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term288 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term485 (x0 : nat -> Prop) (x1 : nat -> Prop) := ((fun y0 : nat -> Prop => (~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x1 y0))) x0) \/ (@FINITE nat x1).
Definition term178 (x0 : nat) (x1 : nat -> Prop) := ~ (exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0).
Definition term478 (x0 : type993) (x1 : Prop) := forall y0 : nat -> Prop, (x0 y0) \/ x1.
Definition term159 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1).
Definition term434 := fun y0 : nat -> Prop => (~ ((exists y1 : nat, @SUBSET nat y0 (dotdot (NUMERAL 0) y1)) -> @FINITE nat y0)) -> (forall y1 : nat, forall y2 : nat, @FINITE nat (dotdot y1 y2)) -> ~ (forall y1 : nat -> Prop, forall y2 : nat -> Prop, ((@FINITE nat y2) /\ (@SUBSET nat y1 y2)) -> @FINITE nat y1).
Definition term422 (x0 : nat -> Prop) := (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)) -> (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0) -> False.
Definition term199 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat -> Prop, ((exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) /\ ((~ (@IN nat y1 y2)) /\ (@FINITE nat y2))) -> exists y3 : nat, forall y4 : nat, ((y4 = y1) \/ (@IN nat y4 y2)) -> Peano.le y4 y3) y0).
Definition term170 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := exists y0 : nat, ~ ((fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 x2) y0).
Definition term486 (x0 : nat -> Prop) := fun y0 : nat -> Prop => ((fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat x0 y1))) y0) \/ (@FINITE nat x0).
Definition term326 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (Peano.le x0 x1)).
Definition term306 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => (((x2 y0) = x0) \/ (@IN nat (x2 y0) x1)) /\ (~ (Peano.le (x2 y0) y0))) x3.
Definition term234 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) /\ (~ (Peano.le y0 x2))) x3.
Definition term516 (x0 : nat -> Prop) (x1 : nat -> Prop) := @eq Prop ((@FINITE nat x0) \/ ((~ (@FINITE nat x1)) \/ (~ (@SUBSET nat x0 x1)))).
Definition term364 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ (Peano.le x1 x0)) -> ~ (@IN nat x1 x2).
Definition term150 := forall y0 : nat, Peano.le y0 y0.
Definition term389 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) /\ ((~ (Peano.le x0 x1)) /\ (Peano.le x2 x3)).
Definition term44 (x0 : nat) (x1 : nat) := True /\ (Peano.le x0 x1).
Definition term22 (a0 : Type') (x0 : type686 a0) := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term237 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y0 y1.
Definition term371 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat (x0 x1) x2.
Definition term430 := (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)) -> ~ (forall y0 : nat -> Prop, forall y1 : nat -> Prop, ((@FINITE nat y1) /\ (@SUBSET nat y0 y1)) -> @FINITE nat y0).
Definition term152 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term505 (x0 : nat) := @FINITE nat (dotdot (NUMERAL 0) x0).
Definition term415 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 x1) x1) -> False.
Definition term254 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0.
Definition term431 (x0 : nat -> Prop) := imp (~ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0)).
Definition term520 (x0 : nat -> Prop) := ~ (~ (@FINITE nat x0)).
Definition term316 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term289 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term386 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x1)) /\ (~ (~ (Peano.le x2 x3))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term263 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0) /\ (exists y1 : nat -> nat, forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term514 (x0 : nat -> Prop) (x1 : nat -> Prop) := (@FINITE nat x0) \/ ((~ (@FINITE nat x1)) \/ (~ (@SUBSET nat x0 x1))).
Definition term499 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term280 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat -> nat => ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term197 (x0 : nat) := fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) /\ (forall y1 : nat, exists y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) /\ (~ (Peano.le y2 y1))).
Definition term103 (x0 : Prop) := forall y0 : nat, x0.
Definition term496 := forall y0 : nat -> Prop, (forall y1 : nat -> Prop, (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat y0 y1))) \/ (@FINITE nat y0).
Definition term68 (x0 : nat) (x1 : nat -> Prop) := (~ (@IN nat x0 x1)) /\ (@FINITE nat x1).
Definition term473 (x0 : nat -> Prop) := forall y0 : nat -> Prop, ((~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0))) \/ (@FINITE nat x0).
Definition term526 (x0 : nat -> Prop) (x1 : nat) := (@FINITE nat (dotdot (NUMERAL 0) x1)) /\ (@SUBSET nat x0 (dotdot (NUMERAL 0) x1)).
Definition term9 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term55 (x0 : nat -> Prop) := imp (@FINITE nat x0).
Definition term97 (x0 : nat) (x1 : nat) := False -> Peano.le x0 x1.
Definition term393 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (Peano.le (x1 x0) x0)) /\ (Peano.le (x1 (x1 x2)) (x1 (x1 x2))).
Definition term417 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (@FINITE nat y0) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x0.
Definition term188 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (forall y0 : nat, exists y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))).
Definition term399 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ ((x0 (x0 x1)) = (x0 x2))) -> ~ ((x0 x1) = x2).
Definition term57 (x0 : nat -> Prop) := (@FINITE nat x0) -> exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term522 (x0 : nat -> Prop) := and (@FINITE nat x0).
Definition term166 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ((x2 = x0) \/ (@IN nat x2 x1)) /\ (~ (Peano.le x2 x3)).
Definition term370 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (~ (@IN nat (x1 x2) x0)) -> (x1 x2) = x3.
Definition term213 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0.
Definition term287 := exists y0 : nat, exists y1 : nat -> Prop, exists y2 : nat, exists y3 : nat -> nat, ((forall y4 : nat, (~ (@IN nat y4 y1)) \/ (Peano.le y4 y2)) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) /\ (forall y4 : nat, (((y3 y4) = y0) \/ (@IN nat (y3 y4) y1)) /\ (~ (Peano.le (y3 y4) y4))).
Definition term283 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, exists y1 : nat -> nat, ((forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term204 := exists y0 : nat, exists y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2)) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) /\ (forall y2 : nat, exists y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) /\ (~ (Peano.le y3 y2))).
Definition term501 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat -> Prop, ((~ (@FINITE nat y1)) \/ (~ (@SUBSET nat y0 y1))) \/ (@FINITE nat y0)) x0.
Definition term376 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 (x0 x1)) (x0 (x0 x1)))) -> Peano.le (x0 (x0 x1)) (x0 (x0 x1)).
Definition term223 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term240 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))) x3 (x2 x3).
Definition term194 (x0 : nat) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1) x1.
Definition term191 (x0 : type993) := exists y0 : nat -> Prop, ~ (x0 y0).
Definition term458 (x0 : nat -> Prop) (x1 : nat) := and ((fun y0 : nat => @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) x1).
Definition term173 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => ~ ((fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 x2) y0).
Definition term531 (x0 : nat -> Prop) := ((@FINITE nat x0) -> exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) /\ ((exists y0 : nat, @SUBSET nat x0 (dotdot (NUMERAL 0) y0)) -> @FINITE nat x0).
Definition term41 (x0 : nat) (x1 : nat) := @IN nat x0 (dotdot (NUMERAL 0) x1).
Definition term442 (x0 : nat) := fun y0 : nat => @FINITE nat (dotdot x0 y0).
Definition term222 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term271 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat -> nat, ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ ((fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x1) \/ (@IN nat (y1 y2) x2)) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term174 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) /\ (~ (Peano.le y0 x2)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term23 (a0 : Type') := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term372 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (~ (@IN nat (x1 (x1 x2)) x0)) -> (x1 (x1 x2)) = x3.
Definition term491 (x0 : nat -> Prop) := forall y0 : nat -> Prop, (~ (@FINITE nat y0)) \/ (~ (@SUBSET nat x0 y0)).
Definition term340 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ ((Peano.le x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term481 (x0 : nat -> Prop) := (forall y0 : nat -> Prop, (fun y1 : nat -> Prop => (~ (@FINITE nat y1)) \/ (~ (@SUBSET nat x0 y1))) y0) \/ (@FINITE nat x0).
Definition term525 (x0 : nat -> Prop) (x1 : nat -> Prop) := imp ((@FINITE nat x1) /\ (@SUBSET nat x0 x1)).
Definition term205 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term286 := fun y0 : nat => exists y1 : nat -> Prop, exists y2 : nat, exists y3 : nat -> nat, ((forall y4 : nat, (~ (@IN nat y4 y1)) \/ (Peano.le y4 y2)) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) /\ (forall y4 : nat, (((y3 y4) = y0) \/ (@IN nat (y3 y4) y1)) /\ (~ (Peano.le (y3 y4) y4))).
Definition term209 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0)) x1.
Definition term89 (x0 : nat -> Prop) := (@FINITE nat x0) -> (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x0.
Definition term382 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term65 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x0.
Definition term181 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0) x2).
Definition term346 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (Peano.le x1 x2).
Definition term158 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (@IN nat x1 x0)) \/ (Peano.le x1 x2).
Definition term46 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) -> @IN nat x1 (dotdot (NUMERAL 0) x2).
Definition term362 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 (x0 x1)) x1) -> ~ (Peano.le (x0 (x0 x1)) x1).
Definition term226 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term428 := imp (forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1)).
Definition term140 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term260 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := and ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))).
Definition term20 (a0 : Type') (x0 : type686 a0) := (x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1)).
Definition term11 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term523 (x0 : nat -> Prop) (x1 : nat -> Prop) := ~ (~ (@SUBSET nat x0 x1)).
Definition term515 (x0 : nat -> Prop) (x1 : nat -> Prop) := @eq Prop ((~ (@FINITE nat x0)) \/ ((~ (@SUBSET nat x1 x0)) \/ (@FINITE nat x1))).
Definition term87 := imp (((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat)) /\ (forall y0 : nat, forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1))).
Definition term509 (x0 : nat -> Prop) (x1 : nat) := ~ (@SUBSET nat x0 (dotdot (NUMERAL 0) x1)).
Definition term319 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term359 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 x1) (x0 (x0 x1))) /\ (~ (Peano.le (x0 x1) x1)).
Definition term168 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term122 (x0 : nat) := fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1.
Definition term78 (x0 : nat) := fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 (@INSERT nat x0 y0)) -> Peano.le y2 y1.
Definition term338 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term264 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (exists y1 : nat -> nat, forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term387 (x0 : nat) (x1 : nat) := and (~ (Peano.le x0 x1)).
Definition term320 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (x0 = x2) -> (x1 x0) = (x1 x2).
Definition term302 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0)) x2.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0).
Definition term310 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat -> Prop) := ((x1 x2) = x0) \/ (@IN nat (x1 x2) x3).
Definition term354 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term143 := imp (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)).
Definition term96 (x0 : nat) (x1 : nat) := (@IN nat x0 (@EMPTY nat)) -> Peano.le x0 x1.
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term325 (x0 : Prop) := x0 -> ~ x0.
Definition term298 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term156 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term243 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => ((y2 = x0) \/ (@IN nat y2 x1)) /\ (~ (Peano.le y2 y1))) y0 (x2 y0).
Definition term7 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term175 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := exists y0 : nat, ((y0 = x0) \/ (@IN nat y0 x1)) /\ (~ (Peano.le y0 x2)).
Definition term397 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ((x1 (x1 x0)) = (x1 x2)) -> ~ ((x1 (x1 x0)) = (x1 x2)).
Definition term270 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x1) \/ (@IN nat (y1 y2) x2)) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term63 := and ((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat)).
Definition term81 := fun y0 : nat => forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1).
Definition term412 (x0 : nat) (x1 : nat -> Prop) := imp (~ (~ (@IN nat x0 x1))).
Definition term321 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (x0 = x2)) \/ ((x1 x0) = (x1 x2)).
Definition term410 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (~ (@IN nat x1 x0))) -> Peano.le x1 x2.
Definition term39 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (@IN nat y0 x0) -> @IN nat y0 (dotdot (NUMERAL 0) x1).
