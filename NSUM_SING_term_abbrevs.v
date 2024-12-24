Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : Prop) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@nsum a0 (@EMPTY a0) x1) = x3) -> ((~ x2) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = y0) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat x2 x3 y0)) x4.
Definition term7 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 (@INSERT a0 y0 y2) y1) = (@COND nat (@IN a0 y0 y2) (@nsum a0 y2 y1) (Nat.add (y1 y0) (@nsum a0 y2 y1))).
Definition term40 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Nat.add (x0 x1) (NUMERAL 0).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : Prop) (x3 : nat) := forall y0 : nat, ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@nsum a0 (@EMPTY a0) x1) = x3) -> ((~ x2) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = y0) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat x2 x3 y0).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : nat) (x3 : nat) := (False -> (@nsum a0 (@EMPTY a0) x1) = x2) -> ((~ False) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = x3) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat False x2 x3).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : nat) (x3 : nat) := ((@IN a0 x0 (@EMPTY a0)) = False) -> (False -> (@nsum a0 (@EMPTY a0) x1) = x2) -> ((~ False) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = x3) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat False x2 x3).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN a0 x0 (@EMPTY a0)) = y0) -> (y0 -> (@nsum a0 (@EMPTY a0) x1) = y1) -> ((~ y0) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = y2) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat y0 y1 y2)) x2.
Definition term50 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @nsum a0 (@INSERT a0 x0 x1) x2.
Definition term52 (a0 : Type') := fun y0 : a0 -> nat => True.
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := @eq nat (@nsum a0 (@INSERT a0 x0 (@EMPTY a0)) x1).
Definition term49 (a0 : Type') := forall y0 : a0, True.
Definition term22 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term55 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> nat, x0.
Definition term2 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term45 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq nat (x0 x1).
Definition term3 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 (@INSERT a0 x0 y1) y0) = (@COND nat (@IN a0 x0 y1) (@nsum a0 y1 y0) (Nat.add (y0 x0) (@nsum a0 y1 y0)))) x1.
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (@FINITE a0 x1) -> (@nsum a0 (@INSERT a0 x0 x1) x2) = (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 x2) (Nat.add (x2 x0) (@nsum a0 x1 x2))).
Definition term51 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0, (@nsum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1).
Definition term1 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term41 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (~ False) -> (Nat.add (x0 x1) (@nsum a0 (@EMPTY a0) x0)) = (x0 x1).
Definition term16 (a0 : Type') := forall y0 : a0 -> nat, (@nsum a0 (@EMPTY a0) y0) = (NUMERAL 0).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : nat) := ((~ False) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = x2) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat False (NUMERAL 0) x2).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : Prop) (x3 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@nsum a0 (@EMPTY a0) x1) = y0) -> ((~ x2) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = y1) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat x2 y0 y1)) x3.
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 (@INSERT a0 x0 y0) x1) = (@COND nat (@IN a0 x0 y0) (@nsum a0 y0 x1) (Nat.add (x1 x0) (@nsum a0 y0 x1))).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@nsum a0 (@EMPTY a0) x1) = y0) -> ((~ x2) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = y1) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat x2 y0 y1).
Definition term39 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Nat.add (x0 x1).
Definition term47 (a0 : Type') := fun y0 : a0 => True.
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 (@INSERT a0 x0 y0) x1) = (@COND nat (@IN a0 x0 y0) (@nsum a0 y0 x1) (Nat.add (x1 x0) (@nsum a0 y0 x1)))) x2.
Definition term42 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := ((~ False) -> (Nat.add (x0 x1) (@nsum a0 (@EMPTY a0) x0)) = (x0 x1)) -> (@COND nat (@IN a0 x1 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x0) (Nat.add (x0 x1) (@nsum a0 (@EMPTY a0) x0))) = (@COND nat False (NUMERAL 0) (x0 x1)).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : Prop) (x3 : nat) (x4 : nat) := ((@IN a0 x0 (@EMPTY a0)) = x2) -> (x2 -> (@nsum a0 (@EMPTY a0) x1) = x3) -> ((~ x2) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = x4) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat x2 x3 x4).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN a0 x0 (@EMPTY a0)) = y0) -> (y0 -> (@nsum a0 (@EMPTY a0) x1) = y1) -> ((~ y0) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = y2) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat y0 y1 y2).
Definition term25 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term24 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := @COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)).
Definition term0 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term9 (a0 : Type') (x0 : a0) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 (@INSERT a0 x0 y1) y0) = (@COND nat (@IN a0 x0 y1) (@nsum a0 y1 y0) (Nat.add (y0 x0) (@nsum a0 y1 y0))).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @COND nat (@IN a0 x0 x1) (@nsum a0 x1 x2) (Nat.add (x2 x0) (@nsum a0 x1 x2)).
Definition term17 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => (@nsum a0 (@EMPTY a0) y0) = (NUMERAL 0)) x0.
Definition term48 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0, (@nsum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term23 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : nat) := (False -> (@nsum a0 (@EMPTY a0) x1) = (NUMERAL 0)) -> ((~ False) -> (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1)) = x2) -> (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))) = (@COND nat False (NUMERAL 0) x2).
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := (@FINITE a0 (@EMPTY a0)) -> (@nsum a0 (@INSERT a0 x0 (@EMPTY a0)) x1) = (@COND nat (@IN a0 x0 (@EMPTY a0)) (@nsum a0 (@EMPTY a0) x1) (Nat.add (x1 x0) (@nsum a0 (@EMPTY a0) x1))).
Definition term6 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term46 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => (@nsum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term36 (a0 : Type') (x0 : a0 -> nat) := False -> (@nsum a0 (@EMPTY a0) x0) = (NUMERAL 0).
Definition term43 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @COND nat False (NUMERAL 0) (x0 x1).
Definition term21 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term8 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 (@INSERT a0 y0 y2) y1) = (@COND nat (@IN a0 y0 y2) (@nsum a0 y2 y1) (Nat.add (y1 y0) (@nsum a0 y2 y1)))) x0.
Definition term53 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0, (@nsum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := @nsum a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term4 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term54 (a0 : Type') := forall y0 : a0 -> nat, True.
