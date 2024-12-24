Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term212 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term162 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ (y0 = x0)) \/ (x1 y0)) x2.
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := ~ (~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))).
Definition term280 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> x1 y0.
Definition term346 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (x0 y0) /\ (~ (x1 y0))) x2.
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term357 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0).
Definition term658 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le (NUMERAL (BIT1 0)) x0) = True.
Definition term188 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term496 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1)).
Definition term630 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term410 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((@SUBSET a0 x3 x1) /\ (@HAS_SIZE a0 x3 x2)) x3.
Definition term171 := (~ False) -> False.
Definition term399 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (((forall y2 : a0, (y0 y2) -> y1 y2) /\ (forall y2 : a0, ~ (y0 y2))) = (forall y2 : a0, ~ (y0 y2)))) -> False) x0.
Definition term397 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0)) \/ ((((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y1 : a0, ~ (x1 y1))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := (@SUBSET a0 x0 x2) /\ ((@FINITE a0 x0) /\ ((Peano.le (@CARD a0 x0) x1) /\ ((@FINITE a0 x2) -> Peano.le x1 (@CARD a0 x2)))).
Definition term65 (a0 : Type') := forall y0 : Prop, (fun y1 : Prop => forall y2 : a0 -> Prop, forall y3 : a0, (y1 /\ (y2 y3)) = ((forall y4 : a0, (y4 = y3) -> y2 y4) /\ y1)) y0.
Definition term568 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2)).
Definition term137 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop ((x1 x0) /\ (exists y0 : a0, (y0 = x0) /\ (~ (x1 y0)))).
Definition term136 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop ((x1 x0) /\ (exists y0 : a0, (fun y1 : a0 => (y1 = x0) /\ (~ (x1 y1))) y0)).
Definition term458 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq ((a0 -> Prop) -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1)).
Definition term457 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq ((a0 -> Prop) -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1)).
Definition term623 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@SUBSET a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (@IN a0 y1 y0)) x0.
Definition term187 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term656 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> (Peano.le (NUMERAL (BIT1 0)) x0) = True.
Definition term431 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (x1 = (@EMPTY a0)) x1.
Definition term501 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) x3 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x2) x3)).
Definition term477 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) x3 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x1) y1) y1))) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x2) x3)).
Definition term427 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) \/ True.
Definition term287 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))).
Definition term274 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 x0) /\ (forall y0 : a0, (@IN a0 y0 x1) = (@IN a0 y0 (@EMPTY a0)))).
Definition term210 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> @FINITE a0 x0.
Definition term260 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : Prop => y0 \/ (~ y0)) (@FINITE a0 x0).
Definition term507 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1)).
Definition term491 (a0 : Type') (x0 : a0 -> Prop) := @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)).
Definition term488 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ (@HAS_SIZE a0 y1 x1)) y1)).
Definition term436 (a0 : Type') := @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (y1 = (@EMPTY a0)) y1)).
Definition term421 (a0 : Type') (x0 : a0 -> Prop) := @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 (NUMERAL 0))) y1)).
Definition term420 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1)).
Definition term633 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term556 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y0) -> @FINITE a0 ((fun y1 : a0 -> Prop => y1) y0).
Definition term70 (a0 : Type') := @eq Prop (forall y0 : Prop, forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0)).
Definition term424 := @eq nat (NUMERAL 0).
Definition term107 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) \/ (x1 x2).
Definition term268 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@SUBSET a0 x0 x1).
Definition term396 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => ((forall y2 : a0, (~ (x1 y2)) \/ (x0 y2)) /\ (forall y2 : a0, ~ (x1 y2))) /\ (x1 y1)) y0) \/ ((fun y1 : a0 => (((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) /\ (forall y2 : a0, ~ (x1 y2))) y0).
Definition term50 (x0 : Prop) := ~ (~ x0).
Definition term522 (a0 : Type') (x0 : type686 a0) := (@FINITE (a0 -> Prop) x0) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @FINITE a0 y0).
Definition term158 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := ((x2 x1) /\ ((x0 = x1) /\ (~ (x2 x0)))) \/ ((~ (x2 x1)) /\ (forall y0 : a0, (~ (y0 = x1)) \/ (x2 y0))).
Definition term608 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => exists y1 : a0 -> Prop, ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) /\ (@IN a0 y0 y1)) x3).
Definition term575 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y2))).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0, (y0 = x0) -> x1 y0) /\ True.
Definition term631 (a0 : Type') (x0 : a0) (x1 : nat) := and (Peano.le (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))) x1).
Definition term448 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @SUBSET a0 y0 x0) x1.
Definition term271 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) /\ (x1 = (@EMPTY a0)).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := ~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2)).
Definition term299 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, (y0 y2) -> y1 y2) /\ (forall y2 : a0, ~ (y0 y2))) = (forall y2 : a0, ~ (y0 y2)).
Definition term401 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@HAS_SIZE a0 y0 (NUMERAL 0)) = (y0 = (@EMPTY a0))) x0.
Definition term311 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) /\ (~ (x1 y0)).
Definition term570 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) := (((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2))) -> (@FINITE a0 x1) = x3) -> (((@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 x2)) -> @FINITE a0 x1) = (((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2))) -> x3).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (False /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ False).
Definition term224 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (x1 x2).
Definition term459 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => @SUBSET a0 y0 x1) x2).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term359 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (exists y0 : a0, ((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)).
Definition term303 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (x1 x2)).
Definition term489 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 y0) y2))) x0.
Definition term134 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (y1 = x0) /\ (~ (x1 y1))) y0.
Definition term230 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((x1 y0) /\ (x2 y0)) y0.
Definition term97 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term342 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term539 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y1) ((fun y2 : a0 -> Prop => y2) y1)).
Definition term319 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term148 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => (x1 x0) /\ ((y1 = x0) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y1 : a0, (~ (y1 = x0)) \/ (x1 y1))).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term261 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) \/ (~ (@FINITE a0 x0)).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term611 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => exists y2 : a0 -> Prop, ((@SUBSET a0 y2 x1) /\ (@HAS_SIZE a0 y2 x2)) /\ (@IN a0 y1 y2)) y0) y0.
Definition term250 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (x1 y3) y3))) /\ (x2 y1)) y0) y0.
Definition term231 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (x1 y1) /\ (x2 y1)) y0) y0.
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y0) /\ ((Peano.le (@CARD a0 y0) y2) /\ ((@FINITE a0 y1) -> Peano.le y2 (@CARD a0 y1))))) -> exists y3 : a0 -> Prop, (@SUBSET a0 y0 y3) /\ ((@SUBSET a0 y3 y1) /\ (@HAS_SIZE a0 y3 y2)).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term480 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) x3 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) /\ (@HAS_SIZE a0 x3 x2)) x3.
Definition term639 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0 -> Prop) := (@FINITE a0 (@INSERT a0 x0 (@EMPTY a0))) /\ ((Peano.le (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))) x1) /\ ((@FINITE a0 x2) -> Peano.le x1 (@CARD a0 x2))).
Definition term283 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 x1).
Definition term536 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) y0) ((fun y1 : a0 -> Prop => y1) y0).
Definition term68 (a0 : Type') := fun y0 : Prop => (fun y1 : Prop => forall y2 : a0 -> Prop, forall y3 : a0, (y1 /\ (y2 y3)) = ((forall y4 : a0, (y4 = y3) -> y2 y4) /\ y1)) y0.
Definition term130 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term43 (x0 : Prop) := (~ x0) -> False.
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term494 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 x0) -> @FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (y0 y2)) y2))) x1.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 x0) /\ ((Peano.le (@CARD a0 x0) x1) /\ ((@FINITE a0 y0) -> Peano.le x1 (@CARD a0 y0))))) -> exists y1 : a0 -> Prop, (@SUBSET a0 x0 y1) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 x1)).
Definition term167 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term363 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => ((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) y0) /\ (forall y0 : a0, ~ (x1 y0)).
Definition term505 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1.
Definition term486 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ (@HAS_SIZE a0 y1 x1)) y1.
Definition term485 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 ((fun y4 : a0 -> Prop => @SUBSET a0 y4 x0) y3) y3))) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1.
Definition term468 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1.
Definition term467 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) y1.
Definition term456 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1.
Definition term434 (a0 : Type') := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (y1 = (@EMPTY a0)) y1.
Definition term417 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 (NUMERAL 0))) y1.
Definition term416 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1.
Definition term395 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (((forall y0 : a0, (~ (x2 y0)) \/ (x0 y0)) /\ (forall y0 : a0, ~ (x2 y0))) /\ (x2 x1)) \/ ((((x2 x1) /\ (~ (x0 x1))) \/ (x2 x1)) /\ (forall y0 : a0, ~ (x2 y0))).
Definition term569 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) := (((@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 x2)) = ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2)))) -> (((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2))) -> (@FINITE a0 x1) = x3) -> (((@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 x2)) -> @FINITE a0 x1) = (((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2))) -> x3).
Definition term592 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0) := @SETSPEC a0 x0 (exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) y0) /\ (@IN a0 x3 ((fun y1 : a0 -> Prop => y1) y0))).
Definition term511 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) -> (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ (@HAS_SIZE a0 y1 x1)) y1))) = True.
Definition term499 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) -> (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1))) = True.
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) \/ False.
Definition term386 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => ((forall y2 : a0, (~ (x1 y2)) \/ (x0 y2)) /\ (forall y2 : a0, ~ (x1 y2))) /\ (x1 y1)) y0).
Definition term349 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (~ (x1 y1))) y0).
Definition term152 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => (x1 x0) /\ ((y1 = x0) /\ (~ (x1 y1)))) y0).
Definition term96 (a0 : Type') := forall y0 : a0, True.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y0) /\ ((Peano.le (@CARD a0 y0) y2) /\ ((@FINITE a0 y1) -> Peano.le y2 (@CARD a0 y1))))) -> exists y3 : a0 -> Prop, (@SUBSET a0 y0 y3) /\ ((@SUBSET a0 y3 y1) /\ (@HAS_SIZE a0 y3 y2))) x0.
Definition term208 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term150 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (x1 x0) /\ ((y1 = x0) /\ (~ (x1 y1)))) y0.
Definition term439 (a0 : Type') (x0 : a0 -> Prop) := @FINITE (a0 -> Prop) (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term530 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := fun y0 : a0 => (x1 /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ x1).
Definition term101 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term523 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @FINITE a0 (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))).
Definition term178 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term545 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))) -> @FINITE a0 x2.
Definition term544 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y1) ((fun y2 : a0 -> Prop => y2) y1)))) -> @FINITE a0 x2.
Definition term640 (x0 : nat) := True /\ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term529 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y0) -> @FINITE a0 ((fun y1 : a0 -> Prop => y1) y0).
Definition term314 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term320 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, x0 y0.
Definition term495 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1)).
Definition term490 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)).
Definition term13 (a0 : Type') := (forall y0 : nat, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ ((@FINITE a0 y1) /\ ((Peano.le (@CARD a0 y1) y0) /\ ((@FINITE a0 y2) -> Peano.le y0 (@CARD a0 y2))))) -> exists y3 : a0 -> Prop, (@SUBSET a0 y1 y3) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 y0))) -> forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y0) /\ ((Peano.le (@CARD a0 y0) y2) /\ ((@FINITE a0 y1) -> Peano.le y2 (@CARD a0 y1))))) -> exists y3 : a0 -> Prop, (@SUBSET a0 y0 y3) /\ ((@SUBSET a0 y3 y1) /\ (@HAS_SIZE a0 y3 y2)).
Definition term129 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (y0 = x0) -> x1 y0.
Definition term126 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or ((x1 x0) /\ (exists y0 : a0, (y0 = x0) /\ (~ (x1 y0)))).
Definition term242 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) /\ (x1 y0).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) \/ (~ (x1 = x2)).
Definition term217 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term466 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 y0 x1) y0.
Definition term249 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x1 y2) y2))) /\ (x2 y0)) y0.
Definition term653 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term355 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (x0 x2))) \/ (x1 x2).
Definition term169 (x0 : Prop) := (~ x0) -> x0.
Definition term579 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y1) ((fun y2 : a0 -> Prop => y2) y1))).
Definition term577 (a0 : Type') (x0 : type686 a0) (x1 : type672 a0) := @UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (x0 y1) (x1 y1))).
Definition term576 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1)).
Definition term195 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := @UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x0 y1) (x1 y1))).
Definition term379 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => ((forall y2 : a0, (~ (x1 y2)) \/ (x0 y2)) /\ (forall y2 : a0, ~ (x1 y2))) /\ (x1 y1)) y0) \/ (exists y0 : a0, (fun y1 : a0 => (((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) /\ (forall y2 : a0, ~ (x1 y2))) y0).
Definition term557 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => ((@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) -> @FINITE a0 y0.
Definition term634 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := Peano.le x0 (@CARD a0 x1).
Definition term259 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((x0 y2) /\ (x1 y2)) y2))) = (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 (x0 y4) y4))) /\ (x1 y2)) y2))).
Definition term383 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((forall y0 : a0, (~ (x1 y0)) \/ (x0 y0)) /\ (forall y0 : a0, ~ (x1 y0))) /\ (x1 x2).
Definition term365 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => ((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) x2.
Definition term601 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, ((@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) /\ (@IN a0 y1 y2)) y1.
Definition term600 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, ((fun y3 : a0 -> Prop => (@SUBSET a0 y3 x0) /\ (@HAS_SIZE a0 y3 x1)) y2) /\ (@IN a0 y1 ((fun y3 : a0 -> Prop => y3) y2))) y1.
Definition term143 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (exists y0 : a0, (x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0)))).
Definition term476 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (@IN (a0 -> Prop) x1 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) /\ (@HAS_SIZE a0 x1 x2).
Definition term493 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 x0) -> @FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (y0 y2)) y2)).
Definition term295 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((forall y1 : a0, (x0 y1) -> y0 y1) /\ (forall y1 : a0, ~ (x0 y1))) = (forall y1 : a0, ~ (x0 y1)).
Definition term591 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := exists y0 : a0 -> Prop, ((@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) /\ (@IN a0 x2 y0).
Definition term512 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) = True.
Definition term498 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (@FINITE (a0 -> Prop) x0) -> (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 x0) /\ (x1 y1)) y1))) = True.
Definition term497 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1))) = True.
Definition term321 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ (forall y0 : a0, (x0 y0) -> x1 y0)).
Definition term193 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : type1470 a0 a1, (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a1, @SETSPEC (a0 -> Prop) y1 (x0 y2) (y0 y2)))) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (exists y3 : a1, (x0 y3) /\ (@IN a0 y2 (y0 y3))) y2)).
Definition term159 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (x1 x0) /\ ((y1 = x0) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y1 : a0, (~ (y1 = x0)) \/ (x1 y1))).
Definition term156 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or ((x1 x0) /\ ((x2 = x0) /\ (~ (x1 x2)))).
Definition term612 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => exists y3 : a0 -> Prop, ((@SUBSET a0 y3 x0) /\ (@HAS_SIZE a0 y3 x1)) /\ (@IN a0 y2 y3)) y1) y1.
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 (x0 y4) y4))) /\ (x1 y2)) y1) y1.
Definition term233 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (x0 y2) /\ (x1 y2)) y1) y1.
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term564 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) = y0) -> (y0 -> (@FINITE a0 x2) = y1) -> (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) -> @FINITE a0 x2) = (y0 -> y1)) x3.
Definition term625 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@SUBSET a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (@IN a0 y0 x0)) x1.
Definition term482 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x1) y2))) /\ (@HAS_SIZE a0 y0 x2)) y0.
Definition term412 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)) y0.
Definition term375 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => ((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) y0) /\ (forall y1 : a0, ~ (x1 y1)).
Definition term661 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))) -> False.
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0) := imp (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term411 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((@SUBSET a0 x2 x1) /\ (@HAS_SIZE a0 x2 (NUMERAL 0))) x2.
Definition term517 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0 -> a1) := (fun y0 : a0 -> a1 => (forall y1 : a1, (@IN a1 y1 (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (x0 y3) (y0 y3)))) -> x1 y1) = (forall y1 : a0, (x0 y1) -> x1 (y0 y1))) x2.
Definition term164 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term334 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) /\ (~ (forall y0 : a0, ~ (x1 y0))).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (~ ((x1 /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ x1))) -> False.
Definition term372 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (((x1 x2) /\ (~ (x0 x2))) \/ (x1 x2)).
Definition term515 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (forall y2 : a1, (@IN a1 y2 (@GSPEC a1 (fun y3 : a1 => exists y4 : a0, @SETSPEC a1 y3 (y0 y4) (y1 y4)))) -> x0 y2) = (forall y2 : a0, (y0 y2) -> x0 (y1 y2))) x1.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 x0) /\ ((Peano.le (@CARD a0 x0) y1) /\ ((@FINITE a0 y0) -> Peano.le y1 (@CARD a0 y0))))) -> exists y2 : a0 -> Prop, (@SUBSET a0 x0 y2) /\ ((@SUBSET a0 y2 y0) /\ (@HAS_SIZE a0 y2 y1))) x1.
Definition term3 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y0) /\ ((Peano.le (@CARD a0 y0) x0) /\ ((@FINITE a0 y1) -> Peano.le x0 (@CARD a0 y1))))) -> exists y2 : a0 -> Prop, (@SUBSET a0 y0 y2) /\ ((@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 x0))) x1.
Definition term77 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0, (True /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ True)) /\ (forall y0 : a0 -> Prop, forall y1 : a0, (False /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ False)).
Definition term376 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y1 : a0, ~ (x1 y1)).
Definition term465 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => @SUBSET a0 y1 x1) y0) y0.
Definition term638 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) /\ True.
Definition term405 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term123 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (x1 x0) /\ (~ (forall y0 : a0, (y0 = x0) -> x1 y0)).
Definition term474 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))).
Definition term473 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x1) y1) y1))).
Definition term595 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0) := @SETSPEC a0 x0 (exists y0 : a0 -> Prop, ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)) /\ (@IN a0 x3 y0)) x3.
Definition term594 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0) := @SETSPEC a0 x0 (exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) y0) /\ (@IN a0 x3 ((fun y1 : a0 -> Prop => y1) y0))) x3.
Definition term302 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) -> x1 x2).
Definition term629 (a0 : Type') (x0 : a0) (x1 : nat) := Peano.le (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))) x1.
Definition term389 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) /\ (forall y2 : a0, ~ (x1 y2))) y0.
Definition term385 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ((forall y2 : a0, (~ (x1 y2)) \/ (x0 y2)) /\ (forall y2 : a0, ~ (x1 y2))) /\ (x1 y1)) y0.
Definition term367 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) y0.
Definition term348 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (~ (x1 y1))) y0.
Definition term151 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (x1 x0) /\ ((y1 = x0) /\ (~ (x1 y1)))) y0.
Definition term135 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (y1 = x0) /\ (~ (x1 y1))) y0.
Definition term345 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => (x1 y1) /\ (~ (x0 y1))) y0) \/ (x1 y0).
Definition term309 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 y1) -> x1 y1) y0).
Definition term114 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (y1 = x0) -> x1 y1) y0).
Definition term516 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := forall y0 : a0 -> a1, (forall y1 : a1, (@IN a1 y1 (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (x0 y3) (y0 y3)))) -> x1 y1) = (forall y1 : a0, (x0 y1) -> x1 (y0 y1)).
Definition term326 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (forall y0 : a0, (~ (x0 y0)) \/ (x1 y0)).
Definition term282 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (forall y0 : a0, (x0 y0) -> x1 y0).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (forall y0 : a0, (y0 = x0) -> x1 y0).
Definition term64 (x0 : Prop -> Prop) := (x0 True) /\ (x0 False).
Definition term413 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 (NUMERAL 0))) y0.
Definition term617 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) y0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)).
Definition term105 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x2 = x0) -> x1 x2).
Definition term560 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term605 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => exists y3 : a0 -> Prop, ((@SUBSET a0 y3 x1) /\ (@HAS_SIZE a0 y3 x2)) /\ (@IN a0 y2 y3)) y1) y1)).
Definition term604 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, ((@SUBSET a0 y2 x1) /\ (@HAS_SIZE a0 y2 x2)) /\ (@IN a0 y1 y2)) y1)).
Definition term255 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (x1 y3) y3))) /\ (x2 y1)) y1)).
Definition term240 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 (x1 y4) y4))) /\ (x2 y2)) y1) y1)).
Definition term236 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((x1 y1) /\ (x2 y1)) y1)).
Definition term221 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (x1 y2) /\ (x2 y2)) y1) y1)).
Definition term190 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term609 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => exists y1 : a0 -> Prop, ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) /\ (@IN a0 y0 y1)) x3) x3.
Definition term463 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => @SUBSET a0 y1 x1) y0) y0.
Definition term333 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and ((forall y0 : a0, (~ (x1 y0)) \/ (x0 y0)) /\ (forall y0 : a0, ~ (x1 y0))).
Definition term332 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and ((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))).
Definition term57 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((x0 /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ x0))) -> False.
Definition term382 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => ((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0)) x2.
Definition term651 (x0 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) x0.
Definition term647 (x0 : nat) := (fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) x0.
Definition term543 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := imp (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) y1))).
Definition term542 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := imp (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x1) /\ (@HAS_SIZE a0 y2 x2)) y1) ((fun y2 : a0 -> Prop => y2) y1)))).
Definition term657 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> (Peano.lt (NUMERAL 0) x0) = True.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term173 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term262 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term289 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0))).
Definition term662 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 y0)) y2))) = ((@FINITE a0 x0) \/ (y0 = (NUMERAL 0))).
Definition term341 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (exists y0 : a0, ((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0)).
Definition term587 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) (x3 : a0 -> Prop) := ((@SUBSET a0 x3 x0) /\ (@HAS_SIZE a0 x3 x1)) /\ (@IN a0 x2 x3).
Definition term588 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y0) /\ (@IN a0 x2 ((fun y1 : a0 -> Prop => y1) y0)).
Definition term364 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => ((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) y0) /\ (forall y1 : a0, ~ (x1 y1)).
Definition term149 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0)))) x2.
Definition term24 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) := @eq Prop (x0 /\ (@IN a0 x1 x2)).
Definition term599 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0, @SETSPEC a0 x0 (exists y1 : a0 -> Prop, ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) /\ (@IN a0 y0 y1)) y0.
Definition term598 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0, @SETSPEC a0 x0 (exists y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x1) /\ (@HAS_SIZE a0 y2 x2)) y1) /\ (@IN a0 y0 ((fun y2 : a0 -> Prop => y2) y1))) y0.
Definition term25 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> Prop) := x0 /\ (@IN a0 x1 x2).
Definition term659 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (@IN a0 x0 x1) -> @IN a0 x0 (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) y1))).
Definition term547 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y2))) -> @FINITE a0 y0.
Definition term546 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((fun y3 : a0 -> Prop => (@SUBSET a0 y3 x0) /\ (@HAS_SIZE a0 y3 x1)) y2) ((fun y3 : a0 -> Prop => y3) y2)))) -> @FINITE a0 y0.
Definition term451 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := ((fun y0 : a0 -> Prop => @SUBSET a0 y0 x0) x2) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x1) x2).
Definition term615 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, ((@SUBSET a0 y2 x1) /\ (@HAS_SIZE a0 y2 x2)) /\ (@IN a0 y1 y2)) y1))).
Definition term614 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => exists y3 : a0 -> Prop, ((@SUBSET a0 y3 x1) /\ (@HAS_SIZE a0 y3 x2)) /\ (@IN a0 y2 y3)) y1) y1))).
Definition term257 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (x1 y3) y3))) /\ (x2 y1)) y1))).
Definition term256 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 (x1 y4) y4))) /\ (x2 y2)) y1) y1))).
Definition term238 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((x1 y1) /\ (x2 y1)) y1))).
Definition term237 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (x1 y2) /\ (x2 y2)) y1) y1))).
Definition term132 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := exists y0 : a0, (x1 x0) /\ ((fun y1 : a0 => (y1 = x0) /\ (~ (x1 y1))) y0).
Definition term584 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := and ((@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 x2)).
Definition term92 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (forall y0 : a0, (y0 = x0) -> x1 y0) /\ False.
Definition term98 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (False /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ False).
Definition term86 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (True /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ True).
Definition term206 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term265 (a0 : Type') := forall y0 : a0, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y2 = y0) y2)) = (@INSERT a0 y0 (@EMPTY a0)).
Definition term356 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (x1 y1) /\ (~ (x0 y1))) y0) \/ (x1 y0).
Definition term374 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (((x2 x1) /\ (~ (x0 x1))) \/ (x2 x1)) /\ (forall y0 : a0, ~ (x2 y0)).
Definition term518 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a1 -> Prop) := forall y0 : a1, (@IN a1 y0 (@GSPEC a1 (fun y1 : a1 => exists y2 : a0, @SETSPEC a1 y1 (x0 y2) (x1 y2)))) -> x2 y0.
Definition term644 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term438 (a0 : Type') := @FINITE (a0 -> Prop) (@INSERT (a0 -> Prop) (@EMPTY a0) (@EMPTY (a0 -> Prop))).
Definition term147 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => (x1 x0) /\ ((y1 = x0) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y0 : a0, (~ (y0 = x0)) \/ (x1 y0))).
Definition term285 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term290 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False) -> (~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False.
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := ((~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False) -> (~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False.
Definition term554 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) x2) -> @FINITE a0 ((fun y0 : a0 -> Prop => y0) x2).
Definition term603 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @IN a0 x0 (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) y1))).
Definition term660 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1)))) /\ (@SUBSET a0 x0 (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1)))).
Definition term209 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term202 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term176 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((~ (x2 = x0)) \/ (x1 x2)).
Definition term624 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@SUBSET a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (@IN a0 y0 x0).
Definition term89 (a0 : Type') := and (forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) = (forall y2 : a0, (y2 = y1) -> y0 y2)).
Definition term74 (a0 : Type') := and (forall y0 : a0 -> Prop, forall y1 : a0, (True /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ True)).
Definition term626 (a0 : Type') (x0 : a0) := and (@FINITE a0 (@INSERT a0 x0 (@EMPTY a0))).
Definition term317 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term426 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) \/ (x1 = (NUMERAL 0)).
Definition term537 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) y0) ((fun y1 : a0 -> Prop => y1) y0).
Definition term567 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) = x3) -> (x3 -> (@FINITE a0 x2) = x4) -> (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) -> @FINITE a0 x2) = (x3 -> x4).
Definition term613 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => exists y3 : a0 -> Prop, ((@SUBSET a0 y3 x0) /\ (@HAS_SIZE a0 y3 x1)) /\ (@IN a0 y2 y3)) y1) y1).
Definition term602 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, ((@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) /\ (@IN a0 y1 y2)) y1).
Definition term580 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, ((fun y3 : a0 -> Prop => (@SUBSET a0 y3 x0) /\ (@HAS_SIZE a0 y3 x1)) y2) /\ (@IN a0 y1 ((fun y3 : a0 -> Prop => y3) y2))) y1).
Definition term578 (a0 : Type') (x0 : type686 a0) (x1 : type672 a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, (x0 y2) /\ (@IN a0 y1 (x1 y2))) y1).
Definition term267 (a0 : Type') (x0 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (y1 = x0) y1).
Definition term254 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 (x0 y4) y4))) /\ (x1 y2)) y1) y1).
Definition term235 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (x0 y2) /\ (x1 y2)) y1) y1).
Definition term219 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (x0 y3) y3))) /\ (x1 y1)) y1).
Definition term218 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((x0 y1) /\ (x1 y1)) y1).
Definition term196 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a1, (x0 y2) /\ (@IN a0 y1 (x1 y2))) y1).
Definition term272 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 x0) /\ (forall y0 : a0, (@IN a0 y0 x1) = (@IN a0 y0 (@EMPTY a0))).
Definition term519 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0 -> a1) := forall y0 : a0, (x0 y0) -> x1 (x2 y0).
Definition term138 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x1 x0) /\ ((fun y0 : a0 => (y0 = x0) /\ (~ (x1 y0))) x2).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (x0 y0) = (forall y1 : a0, (y1 = y0) -> x0 y1).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term398 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0)) \/ ((((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y1 : a0, ~ (x1 y1))).
Definition term161 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := exists y0 : a0, ((x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y1 : a0, (~ (y1 = x0)) \/ (x1 y1))).
Definition term0 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ ((@FINITE a0 y1) /\ ((Peano.le (@CARD a0 y1) y0) /\ ((@FINITE a0 y2) -> Peano.le y0 (@CARD a0 y2))))) -> exists y3 : a0 -> Prop, (@SUBSET a0 y1 y3) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 y0)).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (x0 y0) = (forall y1 : a0, (y1 = y0) -> x0 y1).
Definition term300 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (((forall y2 : a0, (y0 y2) -> y1 y2) /\ (forall y2 : a0, ~ (y0 y2))) = (forall y2 : a0, ~ (y0 y2)))) -> False.
Definition term654 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) x0.
Definition term336 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) /\ (~ (forall y0 : a0, ~ (x1 y0)))).
Definition term226 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((x1 x3) /\ (x2 x3)).
Definition term616 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : nat) := (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x2) /\ ((@SUBSET a0 x2 x1) /\ (@HAS_SIZE a0 x2 x3)).
Definition term607 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => exists y1 : a0 -> Prop, ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) /\ (@IN a0 y0 y1).
Definition term279 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term94 (a0 : Type') := fun y0 : a0 => True.
Definition term337 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (((forall y0 : a0, (~ (x1 y0)) \/ (x0 y0)) /\ (forall y0 : a0, ~ (x1 y0))) /\ (exists y0 : a0, x1 y0)).
Definition term344 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => (x1 y1) /\ (~ (x0 y1))) y0) \/ (exists y0 : a0, x1 y0).
Definition term213 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 x0) /\ ((Peano.le (@CARD a0 x0) x1) /\ ((@FINITE a0 y0) -> Peano.le x1 (@CARD a0 y0))))) -> exists y1 : a0 -> Prop, (@SUBSET a0 x0 y1) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 x1))) x2.
Definition term461 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => @SUBSET a0 y0 x1) x2) x2.
Definition term362 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term404 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term432 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 (y0 = (@EMPTY a0)) y0.
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term610 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => exists y2 : a0 -> Prop, ((@SUBSET a0 y2 x1) /\ (@HAS_SIZE a0 y2 x2)) /\ (@IN a0 y1 y2)) y0) y0.
Definition term248 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (x1 y3) y3))) /\ (x2 y1)) y0) y0.
Definition term229 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (x1 y1) /\ (x2 y1)) y0) y0.
Definition term166 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term270 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0)).
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := exists y0 : a0, (y0 = x0) /\ (~ (x1 y0)).
Definition term251 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x1 y2) y2))) /\ (x2 y0)) y0.
Definition term232 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((x1 y0) /\ (x2 y0)) y0.
Definition term619 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ((@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1) /\ ((@FINITE a0 (@INSERT a0 x0 (@EMPTY a0))) /\ ((Peano.le (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))) x2) /\ ((@FINITE a0 x1) -> Peano.le x2 (@CARD a0 x1))))) -> exists y0 : a0 -> Prop, (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) y0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := ((@SUBSET a0 x0 x1) /\ ((@FINITE a0 x0) /\ ((Peano.le (@CARD a0 x0) x2) /\ ((@FINITE a0 x1) -> Peano.le x2 (@CARD a0 x1))))) -> exists y0 : a0 -> Prop, (@SUBSET a0 x0 y0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)).
Definition term60 (a0 : Type') := fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0).
Definition term59 (a0 : Type') := fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0))) -> False.
Definition term551 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := imp ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) x2).
Definition term141 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0))).
Definition term183 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0))) -> False) x0.
Definition term67 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0)) x0.
Definition term297 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, (x0 y1) -> y0 y1) /\ (forall y1 : a0, ~ (x0 y1))) = (forall y1 : a0, ~ (x0 y1)).
Definition term620 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@CARD a0 (@INSERT a0 y0 (@EMPTY a0))) = (NUMERAL (BIT1 0))) x0.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := fun y0 : a0 => (~ ((x1 /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ x1))) -> False.
Definition term586 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) (x3 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) x3) /\ (@IN a0 x2 ((fun y0 : a0 -> Prop => y0) x3)).
Definition term430 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (x1 = (@EMPTY a0)).
Definition term315 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, ~ (x0 y0)).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (True /\ (x0 x1)).
Definition term447 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x0.
Definition term492 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (y1 y3)) y3))) x0.
Definition term205 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term200 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term197 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) = (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1)) x0.
Definition term328 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ ((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0)))).
Definition term450 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x0) x1.
Definition term27 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (x0 /\ (x1 x2)).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : nat, ((@SUBSET a0 x0 x1) /\ ((@FINITE a0 x0) /\ ((Peano.le (@CARD a0 x0) y0) /\ ((@FINITE a0 x1) -> Peano.le y0 (@CARD a0 x1))))) -> exists y1 : a0 -> Prop, (@SUBSET a0 x0 y1) /\ ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 y0)).
Definition term358 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0).
Definition term222 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2.
Definition term387 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y1 : a0, ~ (x1 y1))) x2.
Definition term338 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) /\ (~ (forall y0 : a0, ~ (x1 y0)))) \/ ((~ ((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0)))) /\ (forall y0 : a0, ~ (x1 y0))).
Definition term115 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (y0 = x0) /\ (~ (x1 y0)).
Definition term1 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ ((@FINITE a0 y1) /\ ((Peano.le (@CARD a0 y1) y0) /\ ((@FINITE a0 y2) -> Peano.le y0 (@CARD a0 y2))))) -> exists y3 : a0 -> Prop, (@SUBSET a0 y1 y3) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 y0))) x0.
Definition term572 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2))) -> (@FINITE a0 x1) = True) -> (((@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 x2)) -> @FINITE a0 x1) = (((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2))) -> True).
Definition term69 (a0 : Type') := @eq Prop (forall y0 : Prop, (fun y1 : Prop => forall y2 : a0 -> Prop, forall y3 : a0, (y1 /\ (y2 y3)) = ((forall y4 : a0, (y4 = y3) -> y2 y4) /\ y1)) y0).
Definition term552 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := imp ((@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 x2)).
Definition term392 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((fun y0 : a0 => ((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0)) x2).
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2.
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) -> @IN a0 y0 x1) /\ x2.
Definition term582 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq (a0 -> Prop) (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))).
Definition term581 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq (a0 -> Prop) (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y1) ((fun y2 : a0 -> Prop => y2) y1)))).
Definition term632 (x0 : nat) := and (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term26 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) (x2 : a0) := x0 /\ (x1 x2).
Definition term354 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => (x1 y0) /\ (~ (x0 y0))) x2) \/ (x1 x2).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := True /\ (x0 x1).
Definition term565 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) (x3 : Prop) := forall y0 : Prop, (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) = x3) -> (x3 -> (@FINITE a0 x2) = y0) -> (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) -> @FINITE a0 x2) = (x3 -> y0).
Definition term561 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term449 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => @SUBSET a0 y0 x0) x1).
Definition term400 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (((forall y1 : a0, (x0 y1) -> y0 y1) /\ (forall y1 : a0, ~ (x0 y1))) = (forall y1 : a0, ~ (x0 y1)))) -> False) x1.
Definition term324 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (x1 y0) /\ (~ (x0 y0))) \/ (exists y0 : a0, x1 y0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (False /\ (x0 x1)).
Definition term140 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (x1 x0) /\ ((fun y1 : a0 => (y1 = x0) /\ (~ (x1 y1))) y0).
Definition term99 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term228 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((x1 x3) /\ (x2 x3)) x3.
Definition term627 (a0 : Type') (x0 : a0) := Peano.le (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))).
Definition term550 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y2))) -> @FINITE a0 y0).
Definition term549 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((fun y3 : a0 -> Prop => (@SUBSET a0 y3 x0) /\ (@HAS_SIZE a0 y3 x1)) y2) ((fun y3 : a0 -> Prop => y3) y2)))) -> @FINITE a0 y0).
Definition term243 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (@IN a0 x2 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x0 y1) y1))) /\ (x1 x2).
Definition term513 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> False.
Definition term75 (a0 : Type') := (fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0)) False.
Definition term157 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := ((fun y0 : a0 => (x2 x1) /\ ((y0 = x1) /\ (~ (x2 y0)))) x0) \/ ((~ (x2 x1)) /\ (forall y0 : a0, (~ (y0 = x1)) \/ (x2 y0))).
Definition term453 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (((fun y0 : a0 -> Prop => @SUBSET a0 y0 x1) x3) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x2) x3)) x3.
Definition term393 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (((forall y0 : a0, (~ (x1 y0)) \/ (x0 y0)) /\ (forall y0 : a0, ~ (x1 y0))) /\ (x1 x2)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (forall y0 : nat, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ ((@FINITE a0 y1) /\ ((Peano.le (@CARD a0 y1) y0) /\ ((@FINITE a0 y2) -> Peano.le y0 (@CARD a0 y2))))) -> exists y3 : a0 -> Prop, (@SUBSET a0 y1 y3) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 y0))) -> exists y0 : a0 -> Prop, (@SUBSET a0 x0 y0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)).
Definition term526 (a0 : Type') (x0 : type686 a0) (x1 : type672 a0) (x2 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (x0 y2) (x1 y2)))) -> x2 y0.
Definition term291 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False) -> (~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False) -> (~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False.
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (((~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False) -> (~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False) -> (~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False.
Definition term296 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (((forall y1 : a0, (x0 y1) -> y0 y1) /\ (forall y1 : a0, ~ (x0 y1))) = (forall y1 : a0, ~ (x0 y1)))) -> False.
Definition term253 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (x0 y3) y3))) /\ (x1 y1)) y1.
Definition term234 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((x0 y1) /\ (x1 y1)) y1.
Definition term182 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x1 = x1) -> x0 x1.
Definition term533 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)) x3).
Definition term203 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term563 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) = y0) -> (y0 -> (@FINITE a0 x2) = y1) -> (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) -> @FINITE a0 x2) = (y0 -> y1).
Definition term562 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term62 (a0 : Type') := forall y0 : Prop, forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0).
Definition term61 (a0 : Type') := forall y0 : Prop, forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0))) -> False.
Definition term325 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))).
Definition term275 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term506 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1).
Definition term487 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ (@HAS_SIZE a0 y1 x1)) y1).
Definition term470 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1).
Definition term469 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) y1).
Definition term445 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 ((fun y4 : a0 -> Prop => @SUBSET a0 y4 x0) y3) y3))) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1).
Definition term444 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1).
Definition term443 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (x0 y3) y3))) /\ (x1 y1)) y1).
Definition term442 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((x0 y1) /\ (x1 y1)) y1).
Definition term437 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (y1 = x0) y1).
Definition term435 (a0 : Type') := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (y1 = (@EMPTY a0)) y1).
Definition term419 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 (NUMERAL 0))) y1).
Definition term418 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1).
Definition term175 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term574 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @SUBSET a0 x0 (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))).
Definition term133 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (y0 = x0) /\ (~ (x1 y0))) x2.
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) -> x1 x2.
Definition term663 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 ((@SUBSET a0 y3 y0) /\ (@HAS_SIZE a0 y3 y1)) y3))) = ((@FINITE a0 y0) \/ (y1 = (NUMERAL 0))).
Definition term514 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (forall y2 : a1, (@IN a1 y2 (@GSPEC a1 (fun y3 : a1 => exists y4 : a0, @SETSPEC a1 y3 (y0 y4) (y1 y4)))) -> x0 y2) = (forall y2 : a0, (y0 y2) -> x0 (y1 y2)).
Definition term301 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((forall y2 : a0, (y0 y2) -> y1 y2) /\ (forall y2 : a0, ~ (y0 y2))) = (forall y2 : a0, ~ (y0 y2)).
Definition term204 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term191 (a0 : Type') (a1 : Type') := forall y0 : a1 -> Prop, forall y1 : type1470 a0 a1, (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a1, @SETSPEC (a0 -> Prop) y2 (y0 y3) (y1 y3)))) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (exists y4 : a1, (y0 y4) /\ (@IN a0 y3 (y1 y4))) y3)).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 x0) /\ ((Peano.le (@CARD a0 x0) y1) /\ ((@FINITE a0 y0) -> Peano.le y1 (@CARD a0 y0))))) -> exists y2 : a0 -> Prop, (@SUBSET a0 x0 y2) /\ ((@SUBSET a0 y2 y0) /\ (@HAS_SIZE a0 y2 y1)).
Definition term2 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y0) /\ ((Peano.le (@CARD a0 y0) x0) /\ ((@FINITE a0 y1) -> Peano.le x0 (@CARD a0 y1))))) -> exists y2 : a0 -> Prop, (@SUBSET a0 y0 y2) /\ ((@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 x0)).
Definition term534 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => y0) x0.
Definition term502 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) x3 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x2) x3)) x3.
Definition term479 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) x3 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x1) y1) y1))) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x2) x3)) x3.
Definition term406 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 x2).
Definition term589 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := fun y0 : a0 -> Prop => ((@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) /\ (@IN a0 x2 y0).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term566 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) = x3) -> (x3 -> (@FINITE a0 x2) = y0) -> (((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) -> @FINITE a0 x2) = (x3 -> y0)) x4.
Definition term645 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) := imp (x0 = x1).
Definition term329 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and ((exists y0 : a0, (x1 y0) /\ (~ (x0 y0))) \/ (exists y0 : a0, x1 y0)).
Definition term66 (a0 : Type') := ((fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0)) True) /\ ((fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0)) False).
Definition term606 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := (fun y0 : a0 => exists y1 : a0 -> Prop, ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) /\ (@IN a0 y0 y1)) x2.
Definition term371 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((fun y0 : a0 => ((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) x2).
Definition term214 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop ((x0 x1) \/ (~ (x1 = x2))).
Definition term269 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) -> @IN a0 y0 x1).
Definition term239 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x0 x2) /\ (x1 x2)).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (x1 x0) /\ (exists y0 : a0, (fun y1 : a0 => (y1 = x0) /\ (~ (x1 y1))) y0).
Definition term71 (a0 : Type') := (fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0)) True.
Definition term276 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((x1 x0) = (forall y0 : a0, (y0 = x0) -> x1 y0)).
Definition term298 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (((forall y2 : a0, (y0 y2) -> y1 y2) /\ (forall y2 : a0, ~ (y0 y2))) = (forall y2 : a0, ~ (y0 y2)))) -> False.
Definition term308 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((fun y0 : a0 => (x0 y0) -> x1 y0) x2).
Definition term113 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((fun y0 : a0 => (y0 = x0) -> x1 y0) x2).
Definition term433 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 (y0 = (@EMPTY a0)) y0.
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (y0 = x0) -> x1 y0.
Definition term571 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := ((@SUBSET a0 x2 x0) /\ ((@FINITE a0 x2) /\ ((@CARD a0 x2) = x1))) -> (@FINITE a0 x2) = True.
Definition term520 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@FINITE a0 (@UNIONS a0 y0)) = ((@FINITE (a0 -> Prop) y0) /\ (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @FINITE a0 y1))) x0.
Definition term360 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, ((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y0 : a0, ~ (x1 y0)).
Definition term590 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y0) /\ (@IN a0 x2 ((fun y1 : a0 -> Prop => y1) y0)).
Definition term316 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term306 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => (x0 y1) -> x1 y1) y0).
Definition term111 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => (y1 = x0) -> x1 y1) y0).
Definition term585 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 ((fun y0 : a0 -> Prop => y0) x1).
Definition term409 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((@SUBSET a0 x2 x1) /\ (@HAS_SIZE a0 x2 (NUMERAL 0))).
Definition term593 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0) := @SETSPEC a0 x0 (exists y0 : a0 -> Prop, ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)) /\ (@IN a0 x3 y0)).
Definition term643 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term378 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, ((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0)) \/ (exists y0 : a0, (((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y1 : a0, ~ (x1 y1))).
Definition term597 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 => @SETSPEC a0 x0 (exists y1 : a0 -> Prop, ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) /\ (@IN a0 y0 y1)) y0.
Definition term596 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 => @SETSPEC a0 x0 (exists y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x1) /\ (@HAS_SIZE a0 y2 x2)) y1) /\ (@IN a0 y0 ((fun y2 : a0 -> Prop => y2) y1))) y0.
Definition term509 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ (@HAS_SIZE a0 y1 x1)) y1))).
Definition term508 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) /\ ((fun y2 : a0 -> Prop => @HAS_SIZE a0 y2 x1) y1)) y1))).
Definition term423 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 (NUMERAL 0))) y1))).
Definition term422 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))).
Definition term117 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (y0 = x0)) \/ (x1 y0).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 (@INSERT a0 x0 (@EMPTY a0))) -> @IN a0 x1 x2.
Definition term373 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := ((fun y0 : a0 => ((x2 y0) /\ (~ (x0 y0))) \/ (x2 y0)) x1) /\ (forall y0 : a0, ~ (x2 y0)).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (False /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ False).
Definition term650 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term646 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term266 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y2 = y0) y2)) = (@INSERT a0 y0 (@EMPTY a0))) x0.
Definition term263 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @FINITE a0 (@INSERT a0 y0 (@EMPTY a0))) x0.
Definition term347 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (x0 y1) /\ (~ (x1 y1))) y0.
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) -> @IN a0 y0 x1.
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x0) \/ (@IN a0 x1 (@EMPTY a0)).
Definition term278 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) -> x1 x2.
Definition term247 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1))) /\ (x2 x3)) x3.
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term63 (x0 : Prop -> Prop) := forall y0 : Prop, x0 y0.
Definition term102 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) = (forall y2 : a0, (y2 = y1) -> y0 y2)) /\ True.
Definition term258 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1))).
Definition term125 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or ((x1 x0) /\ (~ (forall y0 : a0, (y0 = x0) -> x1 y0))).
Definition term446 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => @SUBSET a0 y0 x0.
Definition term172 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term573 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = x2))) -> True.
Definition term380 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => ((forall y2 : a0, (~ (x1 y2)) \/ (x0 y2)) /\ (forall y2 : a0, ~ (x1 y2))) /\ (x1 y1)) y0) \/ ((fun y1 : a0 => (((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) /\ (forall y2 : a0, ~ (x1 y2))) y0).
Definition term154 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : a0, (~ (y0 = x0)) \/ (x1 y0)))).
Definition term153 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (x1 x0) /\ ((y1 = x0) /\ (~ (x1 y1)))) y0) \/ ((~ (x1 x0)) /\ (forall y0 : a0, (~ (y0 = x0)) \/ (x1 y0)))).
Definition term366 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) y0.
Definition term352 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((fun y0 : a0 => (x0 y0) /\ (~ (x1 y0))) x2).
Definition term637 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0 -> Prop) := (Peano.le (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))) x1) /\ ((@FINITE a0 x2) -> Peano.le x1 (@CARD a0 x2)).
Definition term201 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term478 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : nat) := @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) x2 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) /\ (@HAS_SIZE a0 x2 x3)).
Definition term558 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0 -> Prop, ((@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) -> @FINITE a0 y0.
Definition term548 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y2))) -> @FINITE a0 y0.
Definition term528 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((fun y3 : a0 -> Prop => (@SUBSET a0 y3 x0) /\ (@HAS_SIZE a0 y3 x1)) y2) ((fun y3 : a0 -> Prop => y3) y2)))) -> @FINITE a0 y0.
Definition term555 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := ((@SUBSET a0 x2 x0) /\ (@HAS_SIZE a0 x2 x1)) -> @FINITE a0 x2.
Definition term304 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (x1 x2).
Definition term452 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (((fun y0 : a0 -> Prop => @SUBSET a0 y0 x1) x3) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x2) x3)).
Definition term273 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((@SUBSET a0 x1 x0) /\ (x1 = (@EMPTY a0))).
Definition term327 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (~ (x1 y0)) \/ (x0 y0)) /\ (forall y0 : a0, ~ (x1 y0)).
Definition term286 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0)).
Definition term541 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 x2)) y1)).
Definition term540 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x1) /\ (@HAS_SIZE a0 y2 x2)) y1) ((fun y2 : a0 -> Prop => y2) y1))).
Definition term472 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1)).
Definition term471 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x1) y1) y1)).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := False /\ (x0 x1).
Definition term284 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0)).
Definition term384 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ((forall y2 : a0, (~ (x1 y2)) \/ (x0 y2)) /\ (forall y2 : a0, ~ (x1 y2))) /\ (x1 y1)) y0.
Definition term307 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (x0 y0) -> x1 y0) x2.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (fun y0 : nat => ((@SUBSET a0 x0 x1) /\ ((@FINITE a0 x0) /\ ((Peano.le (@CARD a0 x0) y0) /\ ((@FINITE a0 x1) -> Peano.le y0 (@CARD a0 x1))))) -> exists y1 : a0 -> Prop, (@SUBSET a0 x0 y1) /\ ((@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 y0))) x2.
Definition term524 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y2))) -> @FINITE a0 y0).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x1 /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ x1).
Definition term428 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term139 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x1 x0) /\ ((x2 = x0) /\ (~ (x1 x2))).
Definition term124 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (x1 x0) /\ (exists y0 : a0, (y0 = x0) /\ (~ (x1 y0))).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term500 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x1) x2).
Definition term475 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) y1))) /\ ((fun y0 : a0 -> Prop => @HAS_SIZE a0 y0 x1) x2).
Definition term323 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, (x1 y0) -> x0 y0)) \/ (~ (forall y0 : a0, ~ (x1 y0))).
Definition term648 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term462 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 x2 x1) x2.
Definition term56 (a0 : Type') (x0 : Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (x0 /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ x0).
Definition term55 (a0 : Type') (x0 : Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((x0 /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ x0))) -> False.
Definition term312 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) \/ (x1 y0).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0) := (fun y0 : a0 => (~ ((x1 /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ x1))) -> False) x2.
Definition term464 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 y0 x1) y0.
Definition term87 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (y0 y1) = (forall y2 : a0, (y2 = y1) -> y0 y2).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term636 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := False -> Peano.le x0 (@CARD a0 x1).
Definition term339 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((forall y0 : a0, (~ (x1 y0)) \/ (x0 y0)) /\ (forall y0 : a0, ~ (x1 y0))) /\ (exists y0 : a0, x1 y0)) \/ (((exists y0 : a0, (x1 y0) /\ (~ (x0 y0))) \/ (exists y0 : a0, x1 y0)) /\ (forall y0 : a0, ~ (x1 y0))).
Definition term618 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) y0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, (@SUBSET a0 x0 y0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)).
Definition term192 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : type1470 a0 a1, (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a1, @SETSPEC (a0 -> Prop) y2 (y0 y3) (y1 y3)))) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (exists y4 : a1, (y0 y4) /\ (@IN a0 y3 (y1 y4))) y3))) x0.
Definition term429 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) \/ False.
Definition term241 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) /\ (x1 y0)) x2.
Definition term128 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((x1 x0) /\ (exists y0 : a0, (y0 = x0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : a0, (~ (y0 = x0)) \/ (x1 y0))).
Definition term330 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0)))) /\ (forall y0 : a0, ~ (x1 y0)).
Definition term381 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0).
Definition term652 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term211 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term281 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term184 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ ((x0 /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ x0))) -> False) x1.
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False.
Definition term460 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 x1 x2).
Definition term144 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (exists y0 : a0, (x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y0 : a0, (~ (y0 = x0)) \/ (x1 y0))).
Definition term179 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (x2 = x0))) -> x1 x2.
Definition term353 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x0 x2) /\ (~ (x1 x2))).
Definition term370 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, ((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y0 : a0, ~ (x1 y0))).
Definition term369 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => ((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) y0) /\ (forall y0 : a0, ~ (x1 y0))).
Definition term340 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0).
Definition term245 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1))) /\ (x2 x3)).
Definition term292 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False) -> (~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False) -> ((~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False) -> (~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False.
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (((~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False) -> (~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False) -> ((~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False) -> (~ ((x2 /\ (x1 x0)) = ((forall y0 : a0, (y0 = x0) -> x1 y0) /\ x2))) -> False.
Definition term388 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) /\ (forall y2 : a0, ~ (x1 y2))) y0.
Definition term216 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term313 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (x0 y0)) \/ (x1 y0).
Definition term118 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (~ (y0 = x0)) \/ (x1 y0).
Definition term246 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x1 y2) y2))) /\ (x2 y0)) x3) x3.
Definition term227 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (x1 y0) /\ (x2 y0)) x3) x3.
Definition term294 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (((forall y1 : a0, (x0 y1) -> y0 y1) /\ (forall y1 : a0, ~ (x0 y1))) = (forall y1 : a0, ~ (x0 y1)))) -> False.
Definition term521 (a0 : Type') (x0 : type686 a0) := @FINITE a0 (@UNIONS a0 x0).
Definition term277 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) -> @IN a0 x1 x2.
Definition term531 (a0 : Type') := fun y0 : a0 -> Prop => y0.
Definition term655 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term194 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a1, @SETSPEC (a0 -> Prop) y1 (x0 y2) (y0 y2)))) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (exists y3 : a1, (x0 y3) /\ (@IN a0 y2 (y0 y3))) y2))) x1.
Definition term155 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or ((fun y0 : a0 => (x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0)))) x2).
Definition term441 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (True /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ True).
Definition term361 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term288 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))) -> False.
Definition term103 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((x1 x0) = (forall y0 : a0, (y0 = x0) -> x1 y0))) -> False.
Definition term621 (a0 : Type') (x0 : a0) := @CARD a0 (@INSERT a0 x0 (@EMPTY a0)).
Definition term127 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((x1 x0) /\ (~ (forall y0 : a0, (y0 = x0) -> x1 y0))) \/ ((~ (x1 x0)) /\ (forall y0 : a0, (y0 = x0) -> x1 y0)).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (True /\ (x0 y0)) = ((forall y1 : a0, (y1 = y0) -> x0 y1) /\ True).
Definition term220 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((x0 y2) /\ (x1 y2)) y2))) = (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 (x0 y4) y4))) /\ (x1 y2)) y2))).
Definition term199 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0)) x1.
Definition term318 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term293 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (((forall y0 : a0, (x1 y0) -> x0 y0) /\ (forall y0 : a0, ~ (x1 y0))) = (forall y0 : a0, ~ (x1 y0)))).
Definition term112 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (y0 = x0) -> x1 y0) x2.
Definition term635 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> Peano.le x0 (@CARD a0 x1).
Definition term207 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0) x1.
Definition term368 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (exists y0 : a0, (fun y1 : a0 => ((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) y0).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) -> @IN a0 y0 x1.
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1) /\ x2.
Definition term525 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := and (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 x1)) y1))).
Definition term331 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((exists y0 : a0, (x1 y0) /\ (~ (x0 y0))) \/ (exists y0 : a0, x1 y0)) /\ (forall y0 : a0, ~ (x1 y0)).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1).
Definition term642 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term264 (a0 : Type') (x0 : a0) := @FINITE a0 (@INSERT a0 x0 (@EMPTY a0)).
Definition term142 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := exists y0 : a0, (x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0))).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term649 (x0 : nat) := Peano.lt (NUMERAL 0) x0.
Definition term504 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x1) y2))) /\ ((fun y1 : a0 -> Prop => @HAS_SIZE a0 y1 x2) y0)) y0.
Definition term484 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x1) y2))) /\ (@HAS_SIZE a0 y0 x2)) y0.
Definition term483 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((fun y3 : a0 -> Prop => @SUBSET a0 y3 x1) y2) y2))) /\ ((fun y1 : a0 -> Prop => @HAS_SIZE a0 y1 x2) y0)) y0.
Definition term455 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 (((fun y1 : a0 -> Prop => @SUBSET a0 y1 x1) y0) /\ ((fun y1 : a0 -> Prop => @HAS_SIZE a0 y1 x2) y0)) y0.
Definition term415 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 (NUMERAL 0))) y0.
Definition term414 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)) y0.
Definition term343 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term305 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (x0 y0) -> x1 y0).
Definition term110 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (forall y0 : a0, (y0 = x0) -> x1 y0).
Definition term532 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) x2.
Definition term559 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := True /\ (forall y0 : a0 -> Prop, ((@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) -> @FINITE a0 y0).
Definition term538 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (@SUBSET a0 y2 x0) /\ (@HAS_SIZE a0 y2 x1)) y1) ((fun y2 : a0 -> Prop => y2) y1).
Definition term106 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) /\ (~ (x1 x2)).
Definition term186 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
Definition term88 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) = (forall y2 : a0, (y2 = y1) -> y0 y2).
Definition term76 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (False /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ False).
Definition term72 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (True /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ True).
Definition term58 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (x0 /\ (y0 y1)) = ((forall y2 : a0, (y2 = y1) -> y0 y2) /\ x0).
Definition term215 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term322 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (exists y0 : a0, (x0 y0) /\ (~ (x1 y0))).
Definition term394 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => ((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0)) x2) \/ ((fun y0 : a0 => (((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y1 : a0, ~ (x1 y1))) x2).
Definition term335 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (~ (x1 y0)) \/ (x0 y0)) /\ (forall y0 : a0, ~ (x1 y0))) /\ (exists y0 : a0, x1 y0).
Definition term553 (a0 : Type') (x0 : a0 -> Prop) := @FINITE a0 ((fun y0 : a0 -> Prop => y0) x0).
Definition term403 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term73 (a0 : Type') := and ((fun y0 : Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 /\ (y1 y2)) = ((forall y3 : a0, (y3 = y2) -> y1 y3) /\ y0)) True).
Definition term180 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term198 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0).
Definition term223 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) /\ (x1 y0).
Definition term310 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) /\ (~ (x1 y0)).
Definition term622 := NUMERAL (BIT1 0).
Definition term628 := Peano.le (NUMERAL (BIT1 0)).
Definition term377 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y1 : a0, ~ (x1 y1)).
Definition term425 (a0 : Type') (x0 : a0 -> Prop) := or (@FINITE a0 x0).
Definition term121 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (x1 x0)) /\ (forall y0 : a0, (~ (y0 = x0)) \/ (x1 y0)).
Definition term120 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (x1 x0)) /\ (forall y0 : a0, (y0 = x0) -> x1 y0).
Definition term503 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x1) y2))) /\ ((fun y1 : a0 -> Prop => @HAS_SIZE a0 y1 x2) y0)) y0.
Definition term481 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((fun y3 : a0 -> Prop => @SUBSET a0 y3 x1) y2) y2))) /\ ((fun y1 : a0 -> Prop => @HAS_SIZE a0 y1 x2) y0)) y0.
Definition term454 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 (((fun y1 : a0 -> Prop => @SUBSET a0 y1 x1) y0) /\ ((fun y1 : a0 -> Prop => @HAS_SIZE a0 y1 x2) y0)) y0.
Definition term527 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : type672 a0) := forall y0 : a0 -> Prop, (x0 y0) -> x1 (x2 y0).
Definition term408 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : nat) := @SETSPEC (a0 -> Prop) x0 ((@SUBSET a0 x2 x1) /\ (@HAS_SIZE a0 x2 x3)).
Definition term100 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term407 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 (NUMERAL 0)).
Definition term535 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x2)) x3) ((fun y0 : a0 -> Prop => y0) x3).
Definition term641 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0 -> Prop) := (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x2) /\ ((@FINITE a0 (@INSERT a0 x0 (@EMPTY a0))) /\ ((Peano.le (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))) x1) /\ ((@FINITE a0 x2) -> Peano.le x1 (@CARD a0 x2)))).
Definition term181 (a0 : Type') (x0 : a0) (x1 : a0) := imp (~ (~ (x0 = x1))).
Definition term440 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> (@FINITE a0 x0) = False.
Definition term244 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x1 y2) y2))) /\ (x2 y0)) x3).
Definition term225 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (x1 y0) /\ (x2 y0)) x3).
Definition term583 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1)) x2).
Definition term510 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))).
Definition term391 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, ((forall y1 : a0, (~ (x1 y1)) \/ (x0 y1)) /\ (forall y1 : a0, ~ (x1 y1))) /\ (x1 y0)) \/ (exists y0 : a0, (((x1 y0) /\ (~ (x0 y0))) \/ (x1 y0)) /\ (forall y1 : a0, ~ (x1 y1)))).
Definition term390 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => ((forall y2 : a0, (~ (x1 y2)) \/ (x0 y2)) /\ (forall y2 : a0, ~ (x1 y2))) /\ (x1 y1)) y0) \/ (exists y0 : a0, (fun y1 : a0 => (((x1 y1) /\ (~ (x0 y1))) \/ (x1 y1)) /\ (forall y2 : a0, ~ (x1 y2))) y0)).
Definition term351 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (x1 y0) /\ (~ (x0 y0))) \/ (exists y0 : a0, x1 y0)).
Definition term350 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (x1 y1) /\ (~ (x0 y1))) y0) \/ (exists y0 : a0, x1 y0)).
Definition term402 (a0 : Type') (x0 : a0 -> Prop) := @HAS_SIZE a0 x0 (NUMERAL 0).
Definition term160 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 x0) /\ ((y0 = x0) /\ (~ (x1 y0)))) \/ ((~ (x1 x0)) /\ (forall y1 : a0, (~ (y1 = x0)) \/ (x1 y1))).
