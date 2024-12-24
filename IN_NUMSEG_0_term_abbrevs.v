Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (dotdot (NUMERAL 0) x1)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term10 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL 0) x0) /\ (Peano.le x0 x1).
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term17 (x0 : nat) := forall y0 : nat, (@IN nat x0 (dotdot (NUMERAL 0) y0)) = (Peano.le x0 y0).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term11 (x0 : nat) := and (Peano.le (NUMERAL 0) x0).
Definition term21 := fun y0 : nat => forall y1 : nat, (@IN nat y0 (dotdot (NUMERAL 0) y1)) = (Peano.le y0 y1).
Definition term15 (x0 : nat) := fun y0 : nat => (@IN nat x0 (dotdot (NUMERAL 0) y0)) = (Peano.le x0 y0).
Definition term22 := forall y0 : nat, forall y1 : nat, (@IN nat y0 (dotdot (NUMERAL 0) y1)) = (Peano.le y0 y1).
Definition term3 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term18 := forall y0 : nat, True.
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term16 := fun y0 : nat => True.
Definition term5 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term14 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term12 (x0 : nat) (x1 : nat) := True /\ (Peano.le x0 x1).
Definition term20 (x0 : Prop) := forall y0 : nat, x0.
Definition term9 (x0 : nat) (x1 : nat) := @IN nat x0 (dotdot (NUMERAL 0) x1).
