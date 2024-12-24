Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (a0 : Type') (a1 : Type') := dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y0 x1)) = (exists y1 : a0, (x0 = (y0 y1)) /\ (@IN a0 y1 x1)).
Definition term13 (a0 : Type') (a1 : Type') := @IMAGE nat (finite_prod a0 a1) (@mk_finite_prod a0 a1) (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : type36 a0 a1) (x1 : type36 a0 a1) := forall y0 : finite_prod a0 a1, (@IN (finite_prod a0 a1) y0 x0) = (@IN (finite_prod a0 a1) y0 x1).
Definition term14 (a0 : Type') (a1 : Type') := forall y0 : finite_prod a0 a1, (@IN (finite_prod a0 a1) y0 (@UNIV (finite_prod a0 a1))) = (@IN (finite_prod a0 a1) y0 (@IMAGE nat (finite_prod a0 a1) (@mk_finite_prod a0 a1) (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))))).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (@IN a1 y0 (@IMAGE a0 a1 y2 y1)) = (exists y3 : a0, (y0 = (y2 y3)) /\ (@IN a0 y3 y1))) x0.
Definition term19 (a0 : Type') (a1 : Type') (x0 : finite_prod a0 a1) := exists y0 : nat, (x0 = (@mk_finite_prod a0 a1 y0)) /\ (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term15 (a0 : Type') (a1 : Type') (x0 : finite_prod a0 a1) := @eq Prop (@IN (finite_prod a0 a1) x0 (@UNIV (finite_prod a0 a1))).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term17 (a0 : Type') (a1 : Type') (x0 : finite_prod a0 a1) (x1 : type1558 a0 a1) (x2 : nat -> Prop) := exists y0 : nat, (x0 = (x1 y0)) /\ (@IN nat y0 x2).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y1 y0)) = (exists y2 : a0, (x0 = (y1 y2)) /\ (@IN a0 y2 y0))) x1.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 x0 (@IMAGE a0 a1 x1 x2).
Definition term16 (a0 : Type') (a1 : Type') (x0 : finite_prod a0 a1) (x1 : type1558 a0 a1) (x2 : nat -> Prop) := @IN (finite_prod a0 a1) x0 (@IMAGE nat (finite_prod a0 a1) x1 x2).
Definition term7 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term23 (a0 : Type') (a1 : Type') := forall y0 : finite_prod a0 a1, exists y1 : nat, (y0 = (@mk_finite_prod a0 a1 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term21 (a0 : Type') (a1 : Type') := fun y0 : finite_prod a0 a1 => (@IN (finite_prod a0 a1) y0 (@UNIV (finite_prod a0 a1))) = (@IN (finite_prod a0 a1) y0 (@IMAGE nat (finite_prod a0 a1) (@mk_finite_prod a0 a1) (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))))).
Definition term18 (a0 : Type') (a1 : Type') (x0 : finite_prod a0 a1) := @IN (finite_prod a0 a1) x0 (@IMAGE nat (finite_prod a0 a1) (@mk_finite_prod a0 a1) (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y1 y0)) = (exists y2 : a0, (x0 = (y1 y2)) /\ (@IN a0 y2 y0)).
Definition term22 (a0 : Type') (a1 : Type') := fun y0 : finite_prod a0 a1 => exists y1 : nat, (y0 = (@mk_finite_prod a0 a1 y1)) /\ (@IN nat y1 (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (fun y0 : a0 -> a1 => (@IN a1 x0 (@IMAGE a0 a1 y0 x1)) = (exists y1 : a0, (x0 = (y0 y1)) /\ (@IN a0 y1 x1))) x2.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
