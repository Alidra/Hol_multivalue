Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term57 (a0 : Type') := (~ False) -> (S (@CARD a0 (@EMPTY a0))) = (NUMERAL (BIT1 0)).
Definition term64 (a0 : Type') := forall y0 : a0, (@CARD a0 (@INSERT a0 y0 (@EMPTY a0))) = (NUMERAL (BIT1 0)).
Definition term46 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : nat) := forall y0 : nat, ((@IN a0 x0 (@EMPTY a0)) = x1) -> (x1 -> (@CARD a0 (@EMPTY a0)) = x2) -> ((~ x1) -> (S (@CARD a0 (@EMPTY a0))) = y0) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat x1 x2 y0).
Definition term49 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : nat) := ((@IN a0 x0 (@EMPTY a0)) = False) -> (False -> (@CARD a0 (@EMPTY a0)) = x1) -> ((~ False) -> (S (@CARD a0 (@EMPTY a0))) = x2) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat False x1 x2).
Definition term1 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term0 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term4 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term2 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term53 (a0 : Type') (x0 : a0) (x1 : nat) := ((~ False) -> (S (@CARD a0 (@EMPTY a0))) = x1) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat False (NUMERAL 0) x1).
Definition term66 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term22 (x0 : nat) := NUMERAL (S x0).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @CARD a0 (@INSERT a0 x0 x1).
Definition term54 := S (NUMERAL 0).
Definition term8 := (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)).
Definition term15 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term11 (x0 : nat) := forall y0 : nat, ((BIT1 x0) = (BIT1 y0)) = (x0 = y0).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0)))) x1.
Definition term65 (a0 : Type') := forall y0 : a0, True.
Definition term37 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@CARD a0 (@INSERT a0 x0 x1)) = (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))).
Definition term18 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term27 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1)))) x0.
Definition term21 (x0 : nat) := S (NUMERAL x0).
Definition term20 (x0 : nat) := (fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0))) x0.
Definition term6 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))).
Definition term51 (a0 : Type') := False -> (@CARD a0 (@EMPTY a0)) = (NUMERAL 0).
Definition term7 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))).
Definition term60 (a0 : Type') (x0 : a0) := @eq nat (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))).
Definition term55 := NUMERAL (S 0).
Definition term52 (a0 : Type') (x0 : a0) (x1 : nat) := (False -> (@CARD a0 (@EMPTY a0)) = (NUMERAL 0)) -> ((~ False) -> (S (@CARD a0 (@EMPTY a0))) = x1) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat False (NUMERAL 0) x1).
Definition term28 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0))).
Definition term62 (a0 : Type') := fun y0 : a0 => (@CARD a0 (@INSERT a0 y0 (@EMPTY a0))) = (NUMERAL (BIT1 0)).
Definition term44 (a0 : Type') (x0 : a0) (x1 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN a0 x0 (@EMPTY a0)) = x1) -> (x1 -> (@CARD a0 (@EMPTY a0)) = y0) -> ((~ x1) -> (S (@CARD a0 (@EMPTY a0))) = y1) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat x1 y0 y1).
Definition term13 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term9 := forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1).
Definition term63 (a0 : Type') := fun y0 : a0 => True.
Definition term45 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN a0 x0 (@EMPTY a0)) = x1) -> (x1 -> (@CARD a0 (@EMPTY a0)) = y0) -> ((~ x1) -> (S (@CARD a0 (@EMPTY a0))) = y1) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat x1 y0 y1)) x2.
Definition term50 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : nat) := (False -> (@CARD a0 (@EMPTY a0)) = x1) -> ((~ False) -> (S (@CARD a0 (@EMPTY a0))) = x2) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat False x1 x2).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1)).
Definition term35 (a0 : Type') (x0 : a0) := @COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0))).
Definition term47 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((@IN a0 x0 (@EMPTY a0)) = x1) -> (x1 -> (@CARD a0 (@EMPTY a0)) = x2) -> ((~ x1) -> (S (@CARD a0 (@EMPTY a0))) = y0) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat x1 x2 y0)) x3.
Definition term42 (a0 : Type') := S (@CARD a0 (@EMPTY a0)).
Definition term41 (a0 : Type') (x0 : a0) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN a0 x0 (@EMPTY a0)) = y0) -> (y0 -> (@CARD a0 (@EMPTY a0)) = y1) -> ((~ y0) -> (S (@CARD a0 (@EMPTY a0))) = y2) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat y0 y1 y2).
Definition term40 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term39 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term33 (a0 : Type') (x0 : a0) := (@FINITE a0 (@EMPTY a0)) -> (@CARD a0 (@INSERT a0 x0 (@EMPTY a0))) = (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))).
Definition term61 := @eq nat (NUMERAL (BIT1 0)).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)) x0.
Definition term19 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term38 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term43 (a0 : Type') (x0 : a0) (x1 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN a0 x0 (@EMPTY a0)) = y0) -> (y0 -> (@CARD a0 (@EMPTY a0)) = y1) -> ((~ y0) -> (S (@CARD a0 (@EMPTY a0))) = y2) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat y0 y1 y2)) x1.
Definition term58 (a0 : Type') (x0 : a0) := ((~ False) -> (S (@CARD a0 (@EMPTY a0))) = (NUMERAL (BIT1 0))) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat False (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term25 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term3 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term17 := (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))) /\ (((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))))).
Definition term34 (a0 : Type') (x0 : a0) := @CARD a0 (@INSERT a0 x0 (@EMPTY a0)).
Definition term59 := @COND nat False (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((BIT1 x0) = (BIT1 y0)) = (x0 = y0)) x1.
Definition term26 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1))).
Definition term48 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : nat) (x3 : nat) := ((@IN a0 x0 (@EMPTY a0)) = x1) -> (x1 -> (@CARD a0 (@EMPTY a0)) = x2) -> ((~ x1) -> (S (@CARD a0 (@EMPTY a0))) = x3) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@CARD a0 (@EMPTY a0)) (S (@CARD a0 (@EMPTY a0)))) = (@COND nat x1 x2 x3).
Definition term36 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term5 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term56 := NUMERAL (BIT1 0).
Definition term23 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
