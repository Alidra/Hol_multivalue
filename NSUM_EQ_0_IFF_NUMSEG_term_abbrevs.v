Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((@IN nat x3 (dotdot x0 x1)) = x4) -> (x4 -> ((x2 x3) = (NUMERAL 0)) = x5) -> ((@IN nat x3 (dotdot x0 x1)) -> (x2 x3) = (NUMERAL 0)) = (x4 -> x5).
Definition term49 := fun y0 : nat -> nat => True.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term44 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term48 := fun y0 : nat -> nat => forall y1 : nat, forall y2 : nat, ((@nsum nat (dotdot y1 y2) y0) = (NUMERAL 0)) = (forall y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) -> (y0 y3) = (NUMERAL 0)).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) -> (x2 y0) = (NUMERAL 0).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0).
Definition term26 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((@IN nat x2 (dotdot x1 x3)) = ((Peano.le x1 x2) /\ (Peano.le x2 x3))) -> (((Peano.le x1 x2) /\ (Peano.le x2 x3)) -> ((x0 x2) = (NUMERAL 0)) = x4) -> ((@IN nat x2 (dotdot x1 x3)) -> (x0 x2) = (NUMERAL 0)) = (((Peano.le x1 x2) /\ (Peano.le x2 x3)) -> x4).
Definition term50 := forall y0 : nat -> nat, forall y1 : nat, forall y2 : nat, ((@nsum nat (dotdot y1 y2) y0) = (NUMERAL 0)) = (forall y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) -> (y0 y3) = (NUMERAL 0)).
Definition term8 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq Prop (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0)).
Definition term14 (x0 : nat -> Prop) (x1 : nat -> nat) := (@FINITE nat x0) -> ((@nsum nat x0 x1) = (NUMERAL 0)) = (forall y0 : nat, (@IN nat y0 x0) -> (x1 y0) = (NUMERAL 0)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (@FINITE a0 x0) -> ((@nsum a0 x0 x1) = (NUMERAL 0)) = (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (NUMERAL 0)).
Definition term40 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => ((@nsum nat (dotdot x0 y0) x1) = (NUMERAL 0)) = (forall y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) -> (x1 y1) = (NUMERAL 0)).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq Prop (((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0)) = (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0))) = True).
Definition term18 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term42 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, ((@nsum nat (dotdot x0 y0) x1) = (NUMERAL 0)) = (forall y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) -> (x1 y1) = (NUMERAL 0)).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) -> (x2 y0) = (NUMERAL 0).
Definition term51 := forall y0 : nat -> nat, True.
Definition term47 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, ((@nsum nat (dotdot y0 y1) x0) = (NUMERAL 0)) = (forall y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) -> (x0 y2) = (NUMERAL 0)).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq Prop ((fun y0 : Prop => y0 = True) ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0)) = (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0)))).
Definition term46 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, ((@nsum nat (dotdot y0 y1) x0) = (NUMERAL 0)) = (forall y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) -> (x0 y2) = (NUMERAL 0)).
Definition term43 := forall y0 : nat, True.
Definition term41 := fun y0 : nat => True.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := (@IN nat x3 (dotdot x0 x1)) -> (x2 x3) = (NUMERAL 0).
Definition term27 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (((Peano.le x1 x2) /\ (Peano.le x2 x3)) -> ((x0 x2) = (NUMERAL 0)) = x4) -> ((@IN nat x2 (dotdot x1 x3)) -> (x0 x2) = (NUMERAL 0)) = (((Peano.le x1 x2) /\ (Peano.le x2 x3)) -> x4).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((@IN nat x3 (dotdot x0 x1)) = x4) -> (x4 -> ((x2 x3) = (NUMERAL 0)) = y0) -> ((@IN nat x3 (dotdot x0 x1)) -> (x2 x3) = (NUMERAL 0)) = (x4 -> y0).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := (@FINITE nat (dotdot x0 x1)) -> ((@nsum nat (dotdot x0 x1) x2) = (NUMERAL 0)) = (forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) -> (x2 y0) = (NUMERAL 0)).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((@IN nat x3 (dotdot x0 x1)) = y0) -> (y0 -> ((x2 x3) = (NUMERAL 0)) = y1) -> ((@IN nat x3 (dotdot x0 x1)) -> (x2 x3) = (NUMERAL 0)) = (y0 -> y1).
Definition term20 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term11 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> ((@nsum a0 y0 x0) = (NUMERAL 0)) = (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (NUMERAL 0))) x1.
Definition term10 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((@IN nat x3 (dotdot x0 x1)) = x4) -> (x4 -> ((x2 x3) = (NUMERAL 0)) = y0) -> ((@IN nat x3 (dotdot x0 x1)) -> (x2 x3) = (NUMERAL 0)) = (x4 -> y0)) x5.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (NUMERAL 0).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term52 (x0 : Prop) := forall y0 : nat -> nat, x0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq Prop ((@nsum nat (dotdot x0 x1) x2) = (NUMERAL 0)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := ((Peano.le x0 x3) /\ (Peano.le x3 x1)) -> ((x2 x3) = (NUMERAL 0)) = ((x2 x3) = (NUMERAL 0)).
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term45 (x0 : Prop) := forall y0 : nat, x0.
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := (((Peano.le x0 x3) /\ (Peano.le x3 x1)) -> ((x2 x3) = (NUMERAL 0)) = ((x2 x3) = (NUMERAL 0))) -> ((@IN nat x3 (dotdot x0 x1)) -> (x2 x3) = (NUMERAL 0)) = (((Peano.le x0 x3) /\ (Peano.le x3 x1)) -> (x2 x3) = (NUMERAL 0)).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := (fun y0 : Prop => y0 = True) ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0)) = (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (NUMERAL 0))).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN nat x3 (dotdot x0 x1)) = y0) -> (y0 -> ((x2 x3) = (NUMERAL 0)) = y1) -> ((@IN nat x3 (dotdot x0 x1)) -> (x2 x3) = (NUMERAL 0)) = (y0 -> y1)) x4.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @nsum nat (dotdot x0 x1) x2.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat) := ((Peano.le x0 x3) /\ (Peano.le x3 x1)) -> (x2 x3) = (NUMERAL 0).