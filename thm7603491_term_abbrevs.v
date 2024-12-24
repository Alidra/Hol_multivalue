Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term19 := fun y0 : nat -> Prop => y0 (@ε nat y0).
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term27 (a0 : Type') (x0 : nat) := @eq Prop (@IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term22 (a0 : Type') (x0 : finite_image a0) := @finite_index a0 (@dest_finite_image a0 x0).
Definition term14 := and (Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term11 (a0 : Type') := (Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term28 (a0 : Type') := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0).
Definition term15 (a0 : Type') := Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)).
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) x0.
Definition term2 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term18 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term30 (a0 : Type') := (forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) = ((@dest_finite_image a0 (@finite_index a0 y0)) = y0)).
Definition term29 (a0 : Type') := forall y0 : finite_image a0, (@finite_index a0 (@dest_finite_image a0 y0)) = y0.
Definition term16 (a0 : Type') := exists y0 : nat, @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term4 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term23 (a0 : Type') (x0 : nat) := (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) x0.
Definition term20 (a0 : Type') := (fun y0 : nat -> Prop => y0 (@ε nat y0)) (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))).
Definition term6 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term24 (a0 : Type') (x0 : nat) := @dest_finite_image a0 (@finite_index a0 x0).
Definition term25 (a0 : Type') (x0 : nat) := @IN nat x0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term10 (a0 : Type') := @IN nat (NUMERAL (BIT1 0)) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term26 (a0 : Type') (x0 : nat) := @eq Prop ((fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) x0).
Definition term21 (a0 : Type') := (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)))) (@ε nat (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))))).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 x0).
Definition term17 (a0 : Type') := fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
Definition term13 := Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term12 := NUMERAL (BIT1 0).
