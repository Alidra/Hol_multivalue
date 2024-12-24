Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @SETSPEC nat x0 ((Peano.le x1 x2) /\ (Peano.le x2 x3)).
Definition term35 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, @SETSPEC nat x0 ((Peano.le x1 y0) /\ (Peano.le y0 x2)) y0.
Definition term25 (x0 : nat) (x1 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x0 y1) /\ (Peano.le y1 x1)) y1.
Definition term24 (x0 : nat) (x1 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (Peano.le x0 y2) /\ (Peano.le y2 x1)) y1) y1.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x1 y1) /\ (Peano.le y1 x2)) y1))).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (Peano.le x1 y2) /\ (Peano.le y2 x2)) y1) y1))).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@IN nat x0 (dotdot x1 x2)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1)) x2.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term31 (x0 : nat) (x1 : nat) := fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @SETSPEC nat x0 ((fun y0 : nat => (Peano.le x1 y0) /\ (Peano.le y0 x2)) x3).
Definition term40 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1)).
Definition term38 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @SETSPEC nat x0 ((fun y0 : nat => (Peano.le x1 y0) /\ (Peano.le y0 x2)) x3) x3.
Definition term34 := forall y0 : nat, True.
Definition term32 := fun y0 : nat => True.
Definition term33 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term6 (x0 : nat) := forall y0 : nat, (dotdot x0 y0) = (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((Peano.le x0 y2) /\ (Peano.le y2 y0)) y2)).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dotdot x0 y0) = (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((Peano.le x0 y2) /\ (Peano.le y2 y0)) y2))) x1.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => @SETSPEC nat x0 ((Peano.le x1 y0) /\ (Peano.le y0 x2)) y0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dotdot y0 y1) = (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((Peano.le y0 y3) /\ (Peano.le y3 y1)) y3))) x0.
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (Peano.le x1 y2) /\ (Peano.le y2 x2)) y1) y1)).
Definition term11 (x0 : nat) (x1 : nat -> Prop) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (x1 y1) y1)).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x1 y1) /\ (Peano.le y1 x2)) y1)).
Definition term36 (x0 : Prop) := forall y0 : nat, x0.
Definition term14 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @SETSPEC nat x0 ((Peano.le x1 x3) /\ (Peano.le x3 x2)) x3.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => (Peano.le x1 y1) /\ (Peano.le y1 x2)) y0) y0.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => (Peano.le x1 y1) /\ (Peano.le y1 x2)) y0) y0.
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
Definition term37 (x0 : nat) := fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term26 (x0 : nat) (x1 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (Peano.le x0 y2) /\ (Peano.le y2 x1)) y1) y1).
Definition term8 (x0 : nat) (x1 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x0 y1) /\ (Peano.le y1 x1)) y1).
Definition term39 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1)).
