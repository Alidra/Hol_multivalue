Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term58 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0 -> Prop) := ((@IN a0 x1 x2) -> (((fun y0 : a0 => @COND nat (@IN a0 y0 x2) (x0 y0) (NUMERAL 0)) x1) = (x0 x1)) = True) -> ((@IN a0 x1 x2) -> ((fun y0 : a0 => @COND nat (@IN a0 y0 x2) (x0 y0) (NUMERAL 0)) x1) = (x0 x1)) = ((@IN a0 x1 x2) -> True).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((~ x3) -> (NUMERAL 0) = y1) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat x3 y0 y1)) x4.
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : nat) := forall y0 : nat, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (NUMERAL 0) = y0) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat x3 x4 y0).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0)) x2.
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 x0) -> ((fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) y0) = (x1 y0).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := @eq nat ((fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0)) x2).
Definition term65 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0).
Definition term27 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) = (@IN a0 x1 x2)) -> ((@IN a0 x1 x2) -> (((fun y0 : a0 => @COND nat (@IN a0 y0 x2) (x0 y0) (NUMERAL 0)) x1) = (x0 x1)) = x3) -> ((@IN a0 x1 x2) -> ((fun y0 : a0 => @COND nat (@IN a0 y0 x2) (x0 y0) (NUMERAL 0)) x1) = (x0 x1)) = ((@IN a0 x1 x2) -> x3).
Definition term11 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, (forall y3 : a0, (@IN a0 y3 y1) -> (y0 y3) = (y2 y3)) -> (@nsum a0 y1 y0) = (@nsum a0 y1 y2).
Definition term0 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@nsum a0 y2 y0) = (@nsum a0 y2 y1).
Definition term50 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := True -> (x0 x1) = (x0 x1).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> ((fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) y0) = (x1 y0).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (x2 y0).
Definition term64 (a0 : Type') := forall y0 : a0, True.
Definition term13 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, forall y2 : a0 -> nat, (forall y3 : a0, (@IN a0 y3 y1) -> (y0 y3) = (y2 y3)) -> (@nsum a0 y1 y0) = (@nsum a0 y1 y2)) x0.
Definition term1 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@nsum a0 y2 y0) = (@nsum a0 y2 y1)) x0.
Definition term37 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term60 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term8 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@nsum a0 y2 y0) = (@nsum a0 y2 y1)) -> (@nsum a0 x1 x0) = (@nsum a0 x1 x2).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := ((~ True) -> (NUMERAL 0) = (NUMERAL 0)) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat True (x1 x2) (NUMERAL 0)).
Definition term55 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @COND nat True (x0 x1) (NUMERAL 0).
Definition term12 (a0 : Type') := (forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@nsum a0 y2 y0) = (@nsum a0 y2 y1)) -> forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, (forall y3 : a0, (@IN a0 y3 y1) -> (y0 y3) = (y2 y3)) -> (@nsum a0 y1 y0) = (@nsum a0 y1 y2).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := @COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := @eq nat ((fun y0 : a0 => (fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) y0) x2).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) y0) x2.
Definition term56 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq nat (x0 x1).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> (((fun y2 : a0 => @COND nat (@IN a0 y2 x0) (x1 y2) (NUMERAL 0)) x2) = (x1 x2)) = y1) -> ((@IN a0 x2 x0) -> ((fun y2 : a0 => @COND nat (@IN a0 y2 x0) (x1 y2) (NUMERAL 0)) x2) = (x1 x2)) = (y0 -> y1)) x3.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := (True -> (x1 x2) = (x1 x2)) -> ((~ True) -> (NUMERAL 0) = x3) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat True (x1 x2) x3).
Definition term68 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => @COND nat (@IN a0 y1 y0) (x0 y1) (NUMERAL 0))) = (@nsum a0 y0 x0).
Definition term14 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> nat, (forall y2 : a0, (@IN a0 y2 y0) -> (x0 y2) = (y1 y2)) -> (@nsum a0 y0 x0) = (@nsum a0 y0 y1)) x1.
Definition term3 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@nsum a0 y1 x0) = (@nsum a0 y1 y0)) x1.
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) -> (((fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0)) x2) = (x1 x2)) = True.
Definition term18 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((@IN a0 x2 x0) = x3) -> (x3 -> (((fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0)) x2) = (x1 x2)) = x4) -> ((@IN a0 x2 x0) -> ((fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0)) x2) = (x1 x2)) = (x3 -> x4).
Definition term6 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@nsum a0 x1 x0) = (@nsum a0 x1 x2).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) -> ((fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0)) x2) = (x1 x2).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (@FINITE a0 x0) -> (@nsum a0 x0 (fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0))) = (@nsum a0 x0 x1).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((~ x3) -> (NUMERAL 0) = y1) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat x3 y0 y1).
Definition term62 (a0 : Type') := fun y0 : a0 => True.
Definition term30 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) (x4 : nat) := ((@IN a0 x2 x0) = True) -> (True -> (x1 x2) = x3) -> ((~ True) -> (NUMERAL 0) = x4) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat True x3 x4).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x0) -> ((fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) y0) = (x1 y0)) -> (@nsum a0 x0 (fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0))) = (@nsum a0 x0 x1).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((@IN a0 x2 x0) = x3) -> (x3 -> (((fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) x2) = (x1 x2)) = y0) -> ((@IN a0 x2 x0) -> ((fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) x2) = (x1 x2)) = (x3 -> y0).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term15 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (fun y0 : a0 -> nat => (forall y1 : a0, (@IN a0 y1 x1) -> (x0 y1) = (y0 y1)) -> (@nsum a0 x1 x0) = (@nsum a0 x1 y0)) x2.
Definition term5 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@nsum a0 y0 x0) = (@nsum a0 y0 x1)) x2.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN a0 x2 x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((~ y0) -> (NUMERAL 0) = y2) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat y0 y1 y2).
Definition term40 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term39 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> (((fun y2 : a0 => @COND nat (@IN a0 y2 x0) (x1 y2) (NUMERAL 0)) x2) = (x1 x2)) = y1) -> ((@IN a0 x2 x0) -> ((fun y2 : a0 => @COND nat (@IN a0 y2 x0) (x1 y2) (NUMERAL 0)) x2) = (x1 x2)) = (y0 -> y1).
Definition term20 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term28 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) -> (((fun y0 : a0 => @COND nat (@IN a0 y0 x2) (x0 y0) (NUMERAL 0)) x1) = (x0 x1)) = x3) -> ((@IN a0 x1 x2) -> ((fun y0 : a0 => @COND nat (@IN a0 y0 x2) (x0 y0) (NUMERAL 0)) x1) = (x0 x1)) = ((@IN a0 x1 x2) -> x3).
Definition term69 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => @COND nat (@IN a0 y2 y1) (y0 y2) (NUMERAL 0))) = (@nsum a0 y1 y0).
Definition term10 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, (forall y2 : a0, (@IN a0 y2 y0) -> (x0 y2) = (y1 y2)) -> (@nsum a0 y0 x0) = (@nsum a0 y0 y1).
Definition term2 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@nsum a0 y1 x0) = (@nsum a0 y1 y0).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN a0 x2 x0) = x3) -> (x3 -> (((fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) x2) = (x1 x2)) = y0) -> ((@IN a0 x2 x0) -> ((fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) x2) = (x1 x2)) = (x3 -> y0)) x4.
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @nsum a0 x0 (fun y0 : a0 => @COND nat (@IN a0 y0 x0) (x1 y0) (NUMERAL 0)).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : nat) (x5 : nat) := ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (NUMERAL 0) = x5) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat x3 x4 x5).
Definition term38 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) (x4 : nat) := (True -> (x1 x2) = x3) -> ((~ True) -> (NUMERAL 0) = x4) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat True x3 x4).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => (fun y1 : a0 => @COND nat (@IN a0 y1 x0) (x1 y1) (NUMERAL 0)) y0.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := ((~ True) -> (NUMERAL 0) = x3) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat True (x1 x2) x3).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN a0 x2 x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((~ y0) -> (NUMERAL 0) = y2) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat y0 y1 y2)) x3.
Definition term36 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term9 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := forall y0 : a0 -> nat, (forall y1 : a0, (@IN a0 y1 x1) -> (x0 y1) = (y0 y1)) -> (@nsum a0 x1 x0) = (@nsum a0 x1 y0).
Definition term4 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@nsum a0 y0 x0) = (@nsum a0 y0 x1).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : nat) (x5 : nat) := (fun y0 : nat => ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (NUMERAL 0) = y0) -> (@COND nat (@IN a0 x2 x0) (x1 x2) (NUMERAL 0)) = (@COND nat x3 x4 y0)) x5.
Definition term53 := (~ True) -> (NUMERAL 0) = (NUMERAL 0).
