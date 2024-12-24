Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (x0 : nat -> real) (x1 : nat) := @eq real (x0 x1).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := (@IN nat x4 (dotdot x0 x1)) -> ((fun y0 : nat => x2 y0) x4) = (x3 x4).
Definition term33 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) (x5 : Prop) (x6 : Prop) := ((@IN nat x4 (dotdot x0 x1)) = x5) -> (x5 -> (((fun y0 : nat => x2 y0) x4) = (x3 x4)) = x6) -> ((@IN nat x4 (dotdot x0 x1)) -> ((fun y0 : nat => x2 y0) x4) = (x3 x4)) = (x5 -> x6).
Definition term20 (x0 : nat -> real) (x1 : nat -> real) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> (((fun y0 : nat => x0 y0) x3) = (x1 x3)) = x5) -> ((@IN nat x3 (dotdot x2 x4)) -> ((fun y0 : nat => x0 y0) x3) = (x1 x3)) = (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> x5).
Definition term19 (x0 : nat -> real) (x1 : nat -> real) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := ((@IN nat x3 (dotdot x2 x4)) = ((Peano.le x2 x3) /\ (Peano.le x3 x4))) -> (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> (((fun y0 : nat => x0 y0) x3) = (x1 x3)) = x5) -> ((@IN nat x3 (dotdot x2 x4)) -> ((fun y0 : nat => x0 y0) x3) = (x1 x3)) = (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> x5).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := ((Peano.le x0 x4) /\ (Peano.le x4 x1)) -> (((fun y0 : nat => x2 y0) x4) = (x3 x4)) = True.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) (x5 : Prop) (x6 : Prop) := (fun y0 : Prop => ((@IN nat x4 (dotdot x0 x1)) = x5) -> (x5 -> (((fun y1 : nat => x2 y1) x4) = (x3 x4)) = y0) -> ((@IN nat x4 (dotdot x0 x1)) -> ((fun y1 : nat => x2 y1) x4) = (x3 x4)) = (x5 -> y0)) x6.
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) (x5 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN nat x4 (dotdot x0 x1)) = y0) -> (y0 -> (((fun y2 : nat => x2 y2) x4) = (x3 x4)) = y1) -> ((@IN nat x4 (dotdot x0 x1)) -> ((fun y2 : nat => x2 y2) x4) = (x3 x4)) = (y0 -> y1)) x5.
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term26 (x0 : nat -> real) (x1 : nat -> real) (x2 : nat) (x3 : nat) (x4 : nat) := (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> (((fun y0 : nat => x0 y0) x3) = (x1 x3)) = True) -> ((@IN nat x3 (dotdot x2 x4)) -> ((fun y0 : nat => x0 y0) x3) = (x1 x3)) = (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> True).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term14 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term32 := forall y0 : nat, True.
Definition term30 := fun y0 : nat => True.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) (x5 : Prop) := forall y0 : Prop, ((@IN nat x4 (dotdot x0 x1)) = x5) -> (x5 -> (((fun y1 : nat => x2 y1) x4) = (x3 x4)) = y0) -> ((@IN nat x4 (dotdot x0 x1)) -> ((fun y1 : nat => x2 y1) x4) = (x3 x4)) = (x5 -> y0).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := forall y0 : Prop, forall y1 : Prop, ((@IN nat x4 (dotdot x0 x1)) = y0) -> (y0 -> (((fun y2 : nat => x2 y2) x4) = (x3 x4)) = y1) -> ((@IN nat x4 (dotdot x0 x1)) -> ((fun y2 : nat => x2 y2) x4) = (x3 x4)) = (y0 -> y1).
Definition term12 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := ((Peano.le x0 x4) /\ (Peano.le x4 x1)) -> (x2 x4) = (x3 x4).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) -> ((fun y1 : nat => x2 y1) y0) = (x3 y0).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 x1) x2.
Definition term23 (x0 : nat -> real) (x1 : nat) := @eq real ((fun y0 : nat => x0 y0) x1).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := (fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (x3 y0)) x4.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) -> ((fun y1 : nat => x2 y1) y0) = (x3 y0).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (x3 y0).
Definition term34 (x0 : Prop) := forall y0 : nat, x0.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> True.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 x1) (fun y0 : nat => x2 y0).
Definition term22 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
