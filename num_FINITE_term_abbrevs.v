Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := imp ((x1 = x0) \/ (@IN nat x1 x2)).
Definition term23 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term451 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((@IN nat x1 x2) -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1))) = True) -> ((@IN nat x1 x2) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1))) = ((@IN nat x1 x2) -> True).
Definition term363 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term359 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 (x0 x1)) (x0 (x0 x1))) -> ~ (Peano.le (x0 (x0 x1)) (x0 (x0 x1))).
Definition term170 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (~ (exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0)).
Definition term101 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := forall y0 : nat, ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2.
Definition term100 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := forall y0 : nat, (@IN nat y0 (@INSERT nat x0 x1)) -> Peano.le y0 x2.
Definition term374 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))))).
Definition term183 (x0 : nat) := (fun y0 : nat => forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2) x0.
Definition term410 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2)).
Definition term74 := fun y0 : nat -> Prop => (@FINITE nat y0) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0.
Definition term340 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.le x1 x0) /\ (~ (Peano.le x1 x2))).
Definition term437 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x1 x2).
Definition term173 (x0 : type993) := ~ (all x0).
Definition term150 (x0 : nat -> Prop) := ~ (all x0).
Definition term401 := (~ False) -> False.
Definition term260 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat -> nat) := ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ ((fun y0 : nat -> nat => forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))) x3).
Definition term127 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term242 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) x2).
Definition term409 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term339 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2))).
Definition term96 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := (@IN nat x2 (@INSERT nat x0 x1)) -> Peano.le x2 x3.
Definition term179 (x0 : nat) := fun y0 : nat -> Prop => ~ ((fun y1 : nat -> Prop => ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat x0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = x0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2) y0).
Definition term78 := ((exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0) /\ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2)) -> forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1.
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.le x1 x2))).
Definition term389 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (~ (@IN nat (x0 x1) x2)) -> @IN nat (x0 x1) x2.
Definition term384 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ ((x0 x1) = x2).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> @FINITE a0 x0.
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1))) x1.
Definition term145 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0).
Definition term104 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0.
Definition term56 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (@IN nat y1 (@INSERT nat x0 x1)) -> Peano.le y1 y0.
Definition term47 (x0 : nat -> Prop) := exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term43 := exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0.
Definition term403 (x0 : nat -> Prop) := (exists y0 : nat -> Prop, (@FINITE nat y0) /\ (@SUBSET nat x0 y0)) -> @FINITE nat x0.
Definition term84 (x0 : nat) := forall y0 : nat, (@IN nat y0 (@EMPTY nat)) -> Peano.le y0 x0.
Definition term138 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1.
Definition term334 (x0 : Prop) := ~ (~ x0).
Definition term235 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0) /\ (exists y1 : nat -> nat, forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term284 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2)) x0.
Definition term319 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 x1) x1.
Definition term146 (x0 : nat -> Prop) := and (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)).
Definition term49 (x0 : nat -> Prop) := and (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0).
Definition term45 := and (exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0).
Definition term176 (x0 : nat) := exists y0 : nat -> Prop, ~ ((fun y1 : nat -> Prop => ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat x0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = x0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2) y0).
Definition term212 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y0 y1.
Definition term210 (x0 : type1605) := forall y0 : nat, exists y1 : nat, x0 y0 y1.
Definition term167 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, exists y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0)).
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 y0)) x0) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2)).
Definition term291 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2)).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term175 (x0 : nat) := ~ (forall y0 : nat -> Prop, ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1).
Definition term86 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term312 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 (x0 x1)) (x0 x1))) -> Peano.le (x0 x1) (x0 (x0 x1)).
Definition term338 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x0) /\ (~ (Peano.le x1 x2)).
Definition term430 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : Prop) := ((@IN nat x1 x2) = (@IN nat x1 x2)) -> ((@IN nat x1 x2) -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1))) = x3) -> ((@IN nat x1 x2) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1))) = ((@IN nat x1 x2) -> x3).
Definition term18 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term391 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (Peano.le x1 x0) \/ (~ (@IN nat x1 x2)).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term250 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term111 (x0 : Prop) := (~ x0) -> False.
Definition term154 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2) x3.
Definition term279 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term364 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term445 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1.
Definition term444 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x0) y1) y1.
Definition term327 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2)).
Definition term385 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ((x0 x1) = x2) -> ~ ((x0 x1) = x2).
Definition term233 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term452 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1)).
Definition term0 (x0 : nat) := (fun y0 : nat => @FINITE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2))) x0.
Definition term434 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 x0) x1.
Definition term387 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat -> Prop) := @eq Prop (((x1 x2) = x0) \/ (@IN nat (x1 x2) x3)).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term251 (x0 : Prop) (x1 : type1002) := x0 /\ (exists y0 : nat -> nat, x1 y0).
Definition term288 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term310 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term219 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := exists y0 : nat, (fun y1 : nat => fun y2 : nat => ((y2 = x0) \/ (@IN nat y2 x1)) /\ (~ (Peano.le y2 y1))) x2 y0.
Definition term368 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term79 (x0 : nat) := imp (@IN nat x0 (@EMPTY nat)).
Definition term97 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ((x2 = x0) \/ (@IN nat x2 x1)) -> Peano.le x2 x3.
Definition term152 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ (forall y0 : nat, ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2).
Definition term119 := ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term113 := ~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2).
Definition term25 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2))) x0.
Definition term227 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := fun y0 : nat => (((x2 y0) = x0) \/ (@IN nat (x2 y0) x1)) /\ (~ (Peano.le (x2 y0) y0)).
Definition term268 (x0 : nat) := exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat -> nat, ((forall y3 : nat, (~ (@IN nat y3 y0)) \/ (Peano.le y3 y1)) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) /\ (forall y3 : nat, (((y2 y3) = x0) \/ (@IN nat (y2 y3) y0)) /\ (~ (Peano.le (y2 y3) y3))).
Definition term169 (x0 : nat) (x1 : nat -> Prop) := and ((exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term168 (x0 : nat) (x1 : nat -> Prop) := and ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term249 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term379 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (((x1 (x1 x0)) = x2) /\ ((~ (Peano.le (x1 x2) x2)) /\ (Peano.le (x1 (x1 x0)) (x1 (x1 x0))))) -> ~ ((x1 (x1 x0)) = (x1 x2)).
Definition term290 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1)) x2.
Definition term178 (x0 : nat) (x1 : nat -> Prop) := ~ ((fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1) x1).
Definition term372 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x1)) /\ (Peano.le x2 x3).
Definition term317 (x0 : Prop) := (~ x0) -> x0.
Definition term57 (x0 : nat) (x1 : nat -> Prop) := (((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x1) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) -> (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@INSERT nat x0 x1).
Definition term115 := ((~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term204 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := imp (@IN nat x0 (@INSERT nat x1 x2)).
Definition term457 (x0 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0) -> @FINITE nat x0.
Definition term51 (x0 : nat) (x1 : nat -> Prop) := ((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x1) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term448 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term447 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x1) y1) y1))).
Definition term331 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term314 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 x1) (x0 (x0 x1)).
Definition term166 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => exists y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0)).
Definition term208 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term360 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 (x0 x1)) (x0 (x0 x1)).
Definition term325 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2))).
Definition term239 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0).
Definition term197 (x0 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0).
Definition term453 (x0 : nat) (x1 : nat -> Prop) := (@IN nat x0 x1) -> True.
Definition term375 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x3 = x1) /\ ((~ (Peano.le x0 x1)) /\ (Peano.le x2 x3))).
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term232 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1)).
Definition term213 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y1 (y0 y1).
Definition term211 (x0 : type1605) := exists y0 : nat -> nat, forall y1 : nat, x0 y1 (y0 y1).
Definition term365 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x3 = x1))) /\ (~ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term378 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ((x1 (x1 x2)) = x0) /\ ((~ (Peano.le (x1 x0) x0)) /\ (Peano.le (x1 (x1 x2)) (x1 (x1 x2)))).
Definition term426 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN nat x1 x0) = y0) -> (y0 -> (@IN nat x1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 x2) y3))) = y1) -> ((@IN nat x1 x0) -> @IN nat x1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 x2) y3))) = (y0 -> y1)) x3.
Definition term341 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) /\ (~ (Peano.le x0 x2))) -> ~ (Peano.le x1 x2).
Definition term320 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.le x1 x2).
Definition term318 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 x1) x1) -> ~ (Peano.le (x0 x1) x1).
Definition term122 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term357 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := ~ ((x0 (x0 x1)) = x2).
Definition term261 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : nat -> nat) := ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (forall y0 : nat, (((x3 y0) = x1) \/ (@IN nat (x3 y0) x2)) /\ (~ (Peano.le (x3 y0) y0))).
Definition term380 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ~ ((x1 (x1 x0)) = (x1 x2)).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term125 := (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term89 := exists y0 : nat, True.
Definition term285 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1)) x1.
Definition term194 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) x1.
Definition term311 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> Peano.le x0 x1.
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat -> nat, ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term181 (x0 : nat) := exists y0 : nat -> Prop, ((exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) /\ (forall y1 : nat, exists y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) /\ (~ (Peano.le y2 y1))).
Definition term68 := (exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0) /\ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x1 = x0) \/ (@IN nat x1 x2).
Definition term252 (x0 : Prop) (x1 : type1002) := exists y0 : nat -> nat, x0 /\ (x1 y0).
Definition term280 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term144 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0).
Definition term140 (x0 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term133 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term129 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term103 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0.
Definition term102 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => forall y1 : nat, (@IN nat y1 (@INSERT nat x0 x1)) -> Peano.le y1 y0.
Definition term88 := fun y0 : nat => forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0.
Definition term369 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term128 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term42 := (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat).
Definition term193 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term438 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => Peano.le y0 x1) x2) x2.
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat -> nat => ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ ((fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x1) \/ (@IN nat (y1 y2) x2)) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term108 := fun y0 : nat => forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2.
Definition term64 := fun y0 : nat => forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2.
Definition term48 (x0 : nat -> Prop) := and ((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x0).
Definition term148 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ~ (((x2 = x0) \/ (@IN nat x2 x1)) -> Peano.le x2 x3).
Definition term350 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := ~ (@IN nat (x0 (x0 x1)) x2).
Definition term421 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term412 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term405 (x0 : nat -> Prop) (x1 : nat) := @SUBSET nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1)).
Definition term40 := (((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat)) /\ (forall y0 : nat, forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1))) -> forall y0 : nat -> Prop, (@FINITE nat y0) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0.
Definition term390 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := ~ (@IN nat (x0 x1) x2).
Definition term105 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) -> exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0.
Definition term58 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) -> exists y0 : nat, forall y1 : nat, (@IN nat y1 (@INSERT nat x0 x1)) -> Peano.le y1 y0.
Definition term292 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term278 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term419 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (@IN nat y0 x0) -> @IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x1) y2)).
Definition term429 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((@IN nat x1 x0) = x3) -> (x3 -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = x4) -> ((@IN nat x1 x0) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = (x3 -> x4).
Definition term241 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1)))).
Definition term240 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1)))).
Definition term99 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2.
Definition term118 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term436 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => Peano.le y0 x1) x2).
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term76 := forall y0 : nat -> Prop, (@FINITE nat y0) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0.
Definition term137 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) -> Peano.le x1 x2.
Definition term231 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1)).
Definition term230 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y1 (y0 y1).
Definition term257 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))) y0.
Definition term143 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1).
Definition term344 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 (x0 x1)) x1).
Definition term222 (x0 : nat) (x1 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))).
Definition term221 (x0 : nat) (x1 : nat -> Prop) := @eq Prop (forall y0 : nat, exists y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y0 y1).
Definition term386 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (@IN nat (x1 x2) x0) \/ ((x1 x2) = x3).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term201 (x0 : nat -> Prop) (x1 : nat) := and (forall y0 : nat, (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1)).
Definition term110 := True /\ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2).
Definition term77 := forall y0 : nat -> Prop, (@FINITE nat y0) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1.
Definition term91 (x0 : Prop) := exists y0 : nat, x0.
Definition term348 (x0 : nat) (x1 : nat -> Prop) := ~ (@IN nat x0 x1).
Definition term459 := forall y0 : nat -> Prop, (@FINITE nat y0) = (exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1).
Definition term15 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term300 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term296 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x2 x3) = (Peano.le x0 x1)) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term388 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat -> Prop) := (~ ((x1 x2) = x0)) -> @IN nat (x1 x2) x3.
Definition term316 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 x1) (x0 (x0 x1))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term358 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 (x0 x1)) (x0 (x0 x1))).
Definition term224 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) /\ (~ (Peano.le y0 x3))) (x2 x3).
Definition term275 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term256 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat -> nat => (fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))) y0.
Definition term418 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) -> @IN nat y0 x1.
Definition term139 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (@IN nat y0 x0) -> Peano.le y0 x1.
Definition term75 := fun y0 : nat -> Prop => (@FINITE nat y0) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1.
Definition term330 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term283 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term281 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term136 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term134 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term120 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term109 := forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2.
Definition term66 := forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2.
Definition term65 := forall y0 : nat, forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1).
Definition term248 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, ((forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (exists y1 : nat -> nat, forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term255 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1))) x2.
Definition term382 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ ((x0 x1) = (x0 x2))) -> ~ (x1 = x2).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term55 (x0 : nat) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@INSERT nat x0 x1).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) x0) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term234 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x0) \/ (@IN nat (y0 y1) x1)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term159 (x0 : nat -> Prop) := ~ (ex x0).
Definition term163 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0) x2.
Definition term352 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat (x0 (x0 x1)) x2.
Definition term214 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0)).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat x0 (@INSERT nat x1 x2).
Definition term116 := (((~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term1 (x0 : nat) := @FINITE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1)).
Definition term85 := forall y0 : nat, True.
Definition term454 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (@IN nat y0 x0) -> @IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x1) y2)).
Definition term265 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => exists y1 : nat -> nat, ((forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term186 := fun y0 : nat => exists y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2)) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) /\ (forall y2 : nat, exists y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) /\ (~ (Peano.le y3 y2))).
Definition term456 (x0 : nat -> Prop) := fun y0 : nat -> Prop => (@FINITE nat y0) /\ (@SUBSET nat x0 y0).
Definition term439 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x2 x1) x2.
Definition term215 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))) x2.
Definition term349 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (~ (Peano.le (x0 (x0 x1)) x1)) -> ~ (@IN nat (x0 (x0 x1)) x2).
Definition term455 (x0 : nat -> Prop) := exists y0 : nat -> Prop, (@FINITE nat y0) /\ (@SUBSET nat x0 y0).
Definition term21 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term160 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term147 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term52 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term397 (x0 : nat) (x1 : nat -> Prop) := imp (@IN nat x0 x1).
Definition term399 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 x1) x1)) -> Peano.le (x0 x1) x1.
Definition term351 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := (@IN nat (x0 (x0 x1)) x2) -> ~ (@IN nat (x0 (x0 x1)) x2).
Definition term413 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) = (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1)) x0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term301 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term228 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => ((y2 = x0) \/ (@IN nat y2 x1)) /\ (~ (Peano.le y2 y1))) y0 (x2 y0).
Definition term39 (x0 : type993) := ((x0 (@EMPTY nat)) /\ (forall y0 : nat, forall y1 : nat -> Prop, ((x0 y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> x0 (@INSERT nat y0 y1))) -> forall y0 : nat -> Prop, (@FINITE nat y0) -> x0 y0.
Definition term34 (a0 : Type') (x0 : type686 a0) := ((x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term83 := fun y0 : nat => True.
Definition term395 (x0 : nat) (x1 : nat -> Prop) := ~ (~ (@IN nat x0 x1)).
Definition term343 (x0 : nat -> nat) (x1 : nat) := ((Peano.le (x0 x1) (x0 (x0 x1))) /\ (~ (Peano.le (x0 x1) x1))) -> ~ (Peano.le (x0 (x0 x1)) x1).
Definition term259 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop (((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1)))).
Definition term258 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop (((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x1) \/ (@IN nat (y1 y2) x2)) /\ (~ (Peano.le (y1 y2) y2))) y0)).
Definition term274 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term155 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ~ ((fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) -> Peano.le y0 x2) x3).
Definition term191 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term443 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.le y0 x1) y0.
Definition term112 := (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> False.
Definition term435 (x0 : nat) := fun y0 : nat => Peano.le y0 x0.
Definition term53 (x0 : nat) (x1 : nat -> Prop) := imp (((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x1) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term185 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat -> Prop, ((exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) /\ ((~ (@IN nat y1 y2)) /\ (@FINITE nat y2))) -> exists y3 : nat, forall y4 : nat, ((y4 = y1) \/ (@IN nat y4 y2)) -> Peano.le y4 y3) y0).
Definition term165 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 x1)) -> Peano.le y2 y1) y0).
Definition term126 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term298 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term61 (x0 : nat) := forall y0 : nat -> Prop, (((fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) (@INSERT nat x0 y0).
Definition term427 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((@IN nat x1 x0) = x3) -> (x3 -> (@IN nat x1 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x2) y2))) = y0) -> ((@IN nat x1 x0) -> @IN nat x1 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x2) y2))) = (x3 -> y0).
Definition term422 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term67 := ((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat)) /\ (forall y0 : nat, forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1)).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0))) x2.
Definition term82 (x0 : nat) := fun y0 : nat => (@IN nat y0 (@EMPTY nat)) -> Peano.le y0 x0.
Definition term238 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0.
Definition term172 (x0 : nat) (x1 : nat -> Prop) := ~ (((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) -> exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0).
Definition term398 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) := (@IN nat (x1 x2) x0) -> Peano.le (x1 x2) x2.
Definition term117 := (((~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term424 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((@IN nat x1 x0) = y0) -> (y0 -> (@IN nat x1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 x2) y3))) = y1) -> ((@IN nat x1 x0) -> @IN nat x1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 x2) y3))) = (y0 -> y1).
Definition term423 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term16 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term356 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ ((x0 (x0 x1)) = x2)) -> (x0 (x0 x1)) = x2.
Definition term313 (x0 : nat -> nat) (x1 : nat) := x0 (x0 x1).
Definition term431 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) (x3 : Prop) := ((@IN nat x1 x2) -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1))) = x3) -> ((@IN nat x1 x2) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1))) = ((@IN nat x1 x2) -> x3).
Definition term200 (x0 : nat -> Prop) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (@IN nat y1 x0)) \/ (Peano.le y1 y0)) x1).
Definition term367 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term336 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term90 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term333 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x0))) /\ (~ (Peano.le x1 x2)).
Definition term32 (a0 : Type') := forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term132 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term322 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term346 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 (x0 x1)) x1.
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (exists y0 : nat -> nat, forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term2 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term332 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.le x1 x0)) \/ (Peano.le x1 x2)).
Definition term218 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => ((y2 = x0) \/ (@IN nat y2 x1)) /\ (~ (Peano.le y2 y1))) x2 y0.
Definition term376 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = x0) /\ ((~ (Peano.le x3 x0)) /\ (Peano.le x2 x1))) -> ~ (x2 = x3).
Definition term328 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.le x0 x1)) \/ (Peano.le x0 x2))) -> ~ (Peano.le x1 x2).
Definition term315 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 x1) (x0 (x0 x1)))) -> Peano.le (x0 x1) (x0 (x0 x1)).
Definition term225 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) (x3 : nat) := (((x2 x3) = x0) \/ (@IN nat (x2 x3) x1)) /\ (~ (Peano.le (x2 x3) x3)).
Definition term297 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term407 (x0 : nat -> Prop) (x1 : nat) := True /\ (@SUBSET nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term216 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))) x2 x3.
Definition term107 (x0 : nat) := forall y0 : nat -> Prop, ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1.
Definition term62 (x0 : nat) := forall y0 : nat -> Prop, ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 (@INSERT nat x0 y0)) -> Peano.le y2 y1.
Definition term295 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term411 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term428 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN nat x1 x0) = x3) -> (x3 -> (@IN nat x1 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x2) y2))) = y0) -> ((@IN nat x1 x0) -> @IN nat x1 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x2) y2))) = (x3 -> y0)) x4.
Definition term199 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term198 (x0 : nat) (x1 : nat -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term307 (x0 : nat -> nat) (x1 : nat) := Peano.le (x0 (x0 x1)) (x0 x1).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term267 (x0 : nat) := fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat -> nat, ((forall y3 : nat, (~ (@IN nat y3 y0)) \/ (Peano.le y3 y1)) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) /\ (forall y3 : nat, (((y2 y3) = x0) \/ (@IN nat (y2 y3) y0)) /\ (~ (Peano.le (y2 y3) y3))).
Definition term41 := fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1.
Definition term184 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2) x0).
Definition term294 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 x1) x1).
Definition term59 (x0 : nat) := fun y0 : nat -> Prop => (((fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) y0) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> (fun y1 : nat -> Prop => exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) (@INSERT nat x0 y0).
Definition term190 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term33 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) x0.
Definition term162 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 x1)) -> Peano.le y2 y1) y0).
Definition term362 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x1 = x0)) \/ ((Peano.le x3 x0) \/ (~ (Peano.le x2 x1))))) -> ~ (x2 = x3).
Definition term195 (x0 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0.
Definition term70 := imp ((exists y0 : nat, forall y1 : nat, (@IN nat y1 (@EMPTY nat)) -> Peano.le y1 y0) /\ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, (@IN nat y3 (@INSERT nat y0 y1)) -> Peano.le y3 y2)).
Definition term392 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((~ (@IN nat x1 x0)) \/ (Peano.le x1 x2)).
Definition term287 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term98 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => (@IN nat y0 (@INSERT nat x0 x1)) -> Peano.le y0 x2.
Definition term324 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term236 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) x2.
Definition term335 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term441 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.le y0 x1) y0.
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term306 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 (x0 x1)) (x0 x1)) -> ~ (Peano.le (x0 (x0 x1)) (x0 x1)).
Definition term393 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @eq Prop ((Peano.le x1 x0) \/ (~ (@IN nat x1 x2))).
Definition term229 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := forall y0 : nat, (((x2 y0) = x0) \/ (@IN nat (x2 y0) x1)) /\ (~ (Peano.le (x2 y0) y0)).
Definition term305 (x0 : nat -> nat) (x1 : nat) := ~ (Peano.le (x0 (x0 x1)) (x0 x1)).
Definition term207 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term417 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 x0) -> Peano.le y0 x1) x2.
Definition term36 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term406 (x0 : nat -> Prop) (x1 : nat) := (@FINITE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))) /\ (@SUBSET nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term54 (x0 : nat) (x1 : nat -> Prop) := imp ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x1) -> Peano.le y1 y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))).
Definition term271 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term161 (x0 : nat) (x1 : nat -> Prop) := ~ (exists y0 : nat, forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0).
Definition term142 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (@IN nat y0 x0)) \/ (Peano.le y0 x1).
Definition term182 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat -> Prop, ((exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) /\ ((~ (@IN nat y1 y2)) /\ (@FINITE nat y2))) -> exists y3 : nat, forall y4 : nat, ((y4 = y1) \/ (@IN nat y4 y2)) -> Peano.le y4 y3) y0).
Definition term153 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := exists y0 : nat, ~ ((fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 x2) y0).
Definition term449 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) -> (Peano.le x1 x2) = True.
Definition term309 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (Peano.le x0 x1)).
Definition term289 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => (((x2 y0) = x0) \/ (@IN nat (x2 y0) x1)) /\ (~ (Peano.le (x2 y0) y0))) x3.
Definition term217 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) /\ (~ (Peano.le y0 x2))) x3.
Definition term347 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (~ (Peano.le x1 x0)) -> ~ (@IN nat x1 x2).
Definition term373 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) /\ ((~ (Peano.le x0 x1)) /\ (Peano.le x2 x3)).
Definition term37 (a0 : Type') (x0 : type686 a0) := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term220 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => exists y1 : nat, (fun y2 : nat => fun y3 : nat => ((y3 = x0) \/ (@IN nat y3 x1)) /\ (~ (Peano.le y3 y2))) y0 y1.
Definition term354 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat (x0 x1) x2.
Definition term123 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term131 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term400 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 x1) x1) -> False.
Definition term237 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0.
Definition term299 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term433 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x1) y1) y1)).
Definition term432 (x0 : nat) (x1 : nat -> Prop) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (x1 y1) y1)).
Definition term425 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1)).
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term370 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x1)) /\ (~ (~ (Peano.le x2 x3))).
Definition term17 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term246 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) y0) /\ (exists y1 : nat -> nat, forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term416 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := fun y0 : nat -> nat => ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (forall y1 : nat, (((y0 y1) = x1) \/ (@IN nat (y0 y1) x2)) /\ (~ (Peano.le (y0 y1) y1))).
Definition term180 (x0 : nat) := fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (~ (@IN nat y2 y0)) \/ (Peano.le y2 y1)) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) /\ (forall y1 : nat, exists y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) /\ (~ (Peano.le y2 y1))).
Definition term87 (x0 : Prop) := forall y0 : nat, x0.
Definition term50 (x0 : nat) (x1 : nat -> Prop) := (~ (@IN nat x0 x1)) /\ (@FINITE nat x1).
Definition term24 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term71 (x0 : nat -> Prop) := imp (@FINITE nat x0).
Definition term81 (x0 : nat) (x1 : nat) := False -> Peano.le x0 x1.
Definition term377 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (Peano.le (x1 x0) x0)) /\ (Peano.le (x1 (x1 x2)) (x1 (x1 x2))).
Definition term402 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (@FINITE nat y0) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x0.
Definition term171 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (forall y0 : nat, exists y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))).
Definition term383 (x0 : nat -> nat) (x1 : nat) (x2 : nat) := (~ ((x0 (x0 x1)) = (x0 x2))) -> ~ ((x0 x1) = x2).
Definition term73 (x0 : nat -> Prop) := (@FINITE nat x0) -> exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0.
Definition term149 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ((x2 = x0) \/ (@IN nat x2 x1)) /\ (~ (Peano.le x2 x3)).
Definition term353 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (~ (@IN nat (x1 x2) x0)) -> (x1 x2) = x3.
Definition term196 (x0 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x0)) \/ (Peano.le y2 y1)) y0.
Definition term270 := exists y0 : nat, exists y1 : nat -> Prop, exists y2 : nat, exists y3 : nat -> nat, ((forall y4 : nat, (~ (@IN nat y4 y1)) \/ (Peano.le y4 y2)) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) /\ (forall y4 : nat, (((y3 y4) = y0) \/ (@IN nat (y3 y4) y1)) /\ (~ (Peano.le (y3 y4) y4))).
Definition term266 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, exists y1 : nat -> nat, ((forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term187 := exists y0 : nat, exists y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (~ (@IN nat y3 y1)) \/ (Peano.le y3 y2)) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) /\ (forall y2 : nat, exists y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) /\ (~ (Peano.le y3 y2))).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term361 (x0 : nat -> nat) (x1 : nat) := (~ (Peano.le (x0 (x0 x1)) (x0 (x0 x1)))) -> Peano.le (x0 (x0 x1)) (x0 (x0 x1)).
Definition term206 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term223 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) (x3 : nat) := (fun y0 : nat => fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) /\ (~ (Peano.le y1 y0))) x3 (x2 x3).
Definition term177 (x0 : nat) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1) x1.
Definition term174 (x0 : type993) := exists y0 : nat -> Prop, ~ (x0 y0).
Definition term156 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => ~ ((fun y1 : nat => ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 x2) y0).
Definition term458 (x0 : nat -> Prop) := ((@FINITE nat x0) -> exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0) /\ ((exists y0 : nat, forall y1 : nat, (@IN nat y1 x0) -> Peano.le y1 y0) -> @FINITE nat x0).
Definition term205 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term442 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => Peano.le y1 x1) y0) y0.
Definition term254 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := exists y0 : nat -> nat, ((forall y1 : nat, (~ (@IN nat y1 x2)) \/ (Peano.le y1 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ ((fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x1) \/ (@IN nat (y1 y2) x2)) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term157 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => ((y0 = x0) \/ (@IN nat y0 x1)) /\ (~ (Peano.le y0 x2)).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term38 (a0 : Type') := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term355 (x0 : nat -> Prop) (x1 : nat -> nat) (x2 : nat) (x3 : nat) := (~ (@IN nat (x1 (x1 x2)) x0)) -> (x1 (x1 x2)) = x3.
Definition term323 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ ((Peano.le x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term269 := fun y0 : nat => exists y1 : nat -> Prop, exists y2 : nat, exists y3 : nat -> nat, ((forall y4 : nat, (~ (@IN nat y4 y1)) \/ (Peano.le y4 y2)) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) /\ (forall y4 : nat, (((y3 y4) = y0) \/ (@IN nat (y3 y4) y1)) /\ (~ (Peano.le (y3 y4) y4))).
Definition term192 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (@IN nat y2 x1)) \/ (Peano.le y2 y1)) y0) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1)).
Definition term415 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0)) x1.
Definition term72 (x0 : nat -> Prop) := (@FINITE nat x0) -> (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x0.
Definition term366 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term46 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) x0.
Definition term164 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ~ ((fun y0 : nat => forall y1 : nat, ((y1 = x0) \/ (@IN nat y1 x1)) -> Peano.le y1 y0) x2).
Definition term329 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ (Peano.le x1 x2).
Definition term141 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (@IN nat x1 x0)) \/ (Peano.le x1 x2).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0) x1.
Definition term440 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => Peano.le y1 x1) y0) y0.
Definition term345 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 (x0 x1)) x1) -> ~ (Peano.le (x0 (x0 x1)) x1).
Definition term404 (x0 : nat) := and (@FINITE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1))).
Definition term209 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term121 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := and ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))).
Definition term35 (a0 : Type') (x0 : type686 a0) := (x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1)).
Definition term26 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term69 := imp (((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat)) /\ (forall y0 : nat, forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1))).
Definition term302 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term114 := (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term342 (x0 : nat -> nat) (x1 : nat) := (Peano.le (x0 x1) (x0 (x0 x1))) /\ (~ (Peano.le (x0 x1) x1)).
Definition term151 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term106 (x0 : nat) := fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, ((y2 = x0) \/ (@IN nat y2 y0)) -> Peano.le y2 y1.
Definition term60 (x0 : nat) := fun y0 : nat -> Prop => ((exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) /\ ((~ (@IN nat x0 y0)) /\ (@FINITE nat y0))) -> exists y1 : nat, forall y2 : nat, (@IN nat y2 (@INSERT nat x0 y0)) -> Peano.le y2 y1.
Definition term408 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
Definition term321 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term247 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => ((forall y1 : nat, (~ (@IN nat y1 x1)) \/ (Peano.le y1 y0)) /\ ((~ (@IN nat x0 x1)) /\ (@FINITE nat x1))) /\ (exists y1 : nat -> nat, forall y2 : nat, (((y1 y2) = x0) \/ (@IN nat (y1 y2) x1)) /\ (~ (Peano.le (y1 y2) y2))).
Definition term13 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term371 (x0 : nat) (x1 : nat) := and (~ (Peano.le x0 x1)).
Definition term303 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (x0 = x2) -> (x1 x0) = (x1 x2).
Definition term286 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0)) x2.
Definition term414 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0).
Definition term293 (x0 : nat) (x1 : nat -> nat) (x2 : nat) (x3 : nat -> Prop) := ((x1 x2) = x0) \/ (@IN nat (x1 x2) x3).
Definition term337 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term446 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x0) y1) y1).
Definition term420 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1).
Definition term124 := imp (~ (forall y0 : nat, forall y1 : nat -> Prop, ((exists y2 : nat, forall y3 : nat, (@IN nat y3 y1) -> Peano.le y3 y2) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> exists y2 : nat, forall y3 : nat, ((y3 = y0) \/ (@IN nat y3 y1)) -> Peano.le y3 y2)).
Definition term80 (x0 : nat) (x1 : nat) := (@IN nat x0 (@EMPTY nat)) -> Peano.le x0 x1.
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term308 (x0 : Prop) := x0 -> ~ x0.
Definition term282 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term135 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term226 (x0 : nat) (x1 : nat -> Prop) (x2 : nat -> nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => ((y2 = x0) \/ (@IN nat y2 x1)) /\ (~ (Peano.le y2 y1))) y0 (x2 y0).
Definition term22 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term158 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := exists y0 : nat, ((y0 = x0) \/ (@IN nat y0 x1)) /\ (~ (Peano.le y0 x2)).
Definition term450 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@IN nat x1 x0) -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = True.
Definition term381 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := ((x1 (x1 x0)) = (x1 x2)) -> ~ ((x1 (x1 x0)) = (x1 x2)).
Definition term253 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := ((forall y0 : nat, (~ (@IN nat y0 x2)) \/ (Peano.le y0 x0)) /\ ((~ (@IN nat x1 x2)) /\ (@FINITE nat x2))) /\ (exists y0 : nat -> nat, (fun y1 : nat -> nat => forall y2 : nat, (((y1 y2) = x1) \/ (@IN nat (y1 y2) x2)) /\ (~ (Peano.le (y1 y2) y2))) y0).
Definition term44 := and ((fun y0 : nat -> Prop => exists y1 : nat, forall y2 : nat, (@IN nat y2 y0) -> Peano.le y2 y1) (@EMPTY nat)).
Definition term63 := fun y0 : nat => forall y1 : nat -> Prop, (((fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) y1) /\ ((~ (@IN nat y0 y1)) /\ (@FINITE nat y1))) -> (fun y2 : nat -> Prop => exists y3 : nat, forall y4 : nat, (@IN nat y4 y2) -> Peano.le y4 y3) (@INSERT nat y0 y1).
Definition term396 (x0 : nat) (x1 : nat -> Prop) := imp (~ (~ (@IN nat x0 x1))).
Definition term304 (x0 : nat) (x1 : nat -> nat) (x2 : nat) := (~ (x0 = x2)) \/ ((x1 x0) = (x1 x2)).
Definition term394 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (~ (@IN nat x1 x0))) -> Peano.le x1 x2.
