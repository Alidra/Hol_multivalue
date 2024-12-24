Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) := forall y0 : nat, (x1 (S y0)) = (x0 (x1 y0)).
Definition term0 (a0 : Type') (x0 : nat -> a0) := x0 (NUMERAL 0).
Definition term8 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term4 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) (x2 : nat) := x0 (x1 x2).
Definition term19 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) := forall y0 : nat, (x1 (S y0)) = ((fun y1 : a0 => fun y2 : nat => x0 y1) (x1 y0) y0).
Definition term14 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : a0 => fun y1 : nat => x0 y0) (x1 x2) x2.
Definition term3 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := x0 (S x1).
Definition term6 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> a0) := fun y0 : nat -> a0 => ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1))).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> a0) := fun y0 : nat -> a0 => ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : a0 => fun y3 : nat => x1 y2) (y0 y1) y1)).
Definition term11 (a0 : Type') (x0 : a0 -> a0) := fun y0 : a0 => fun y1 : nat => x0 y0.
Definition term18 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) := fun y0 : nat => (x1 (S y0)) = (x0 (x1 y0)).
Definition term20 (a0 : Type') (x0 : nat -> a0) (x1 : a0) := and ((x0 (NUMERAL 0)) = x1).
Definition term15 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => x0 (x1 x2)) x2.
Definition term2 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => (x1 (S y0)) = (x0 (x1 y0))) x2.
Definition term17 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) := fun y0 : nat => (x1 (S y0)) = ((fun y1 : a0 => fun y2 : nat => x0 y1) (x1 y0) y0).
Definition term12 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : a0 => fun y1 : nat => x0 y0) (x1 x2).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> a0) (x2 : nat -> a0) := ((x2 (NUMERAL 0)) = x0) /\ (forall y0 : nat, (x2 (S y0)) = ((fun y1 : a0 => fun y2 : nat => x1 y1) (x2 y0) y0)).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0 -> a0) (x2 : nat -> a0) := ((x2 (NUMERAL 0)) = x0) /\ (forall y0 : nat, (x2 (S y0)) = (x1 (x2 y0))).
Definition term7 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term16 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @eq a0 (x0 (S x1)).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0 -> a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1))).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0 -> a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : a0 => fun y3 : nat => x1 y2) (y0 y1) y1)).
Definition term9 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term13 (a0 : Type') (x0 : a0 -> a0) (x1 : nat -> a0) (x2 : nat) := fun y0 : nat => x0 (x1 x2).
