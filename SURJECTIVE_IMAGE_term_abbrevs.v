Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1) := fun y0 : a0 => (@IN a0 y0 (@UNIV a0)) /\ ((x0 y0) = x1).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := ((forall y0 : a1 -> Prop, exists y1 : a0 -> Prop, (@IMAGE a0 a1 x0 y1) = y0) = (forall y0 : a1, exists y1 : a0, (x0 y1) = y0)) -> (forall y0 : a1 -> Prop, exists y1 : a0 -> Prop, (@IMAGE a0 a1 x0 y1) = y0) = (forall y0 : a1, exists y1 : a0, (x0 y1) = y0).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := ((forall y0 : a1 -> Prop, (@SUBSET a1 y0 (@UNIV a1)) -> exists y1 : a0 -> Prop, (@SUBSET a0 y1 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y1) = y0)) = (forall y0 : a1, (@IN a1 y0 (@UNIV a1)) -> exists y1 : a0, (@IN a0 y1 (@UNIV a0)) /\ ((x0 y1) = y0))) -> (forall y0 : a1 -> Prop, exists y1 : a0 -> Prop, (@IMAGE a0 a1 x0 y1) = y0) = (forall y0 : a1, exists y1 : a0, (x0 y1) = y0).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) := exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y0) = x1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a1 -> Prop => exists y1 : a0 -> Prop, (@IMAGE a0 a1 x0 y1) = y0.
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a1 => exists y1 : a0, (x0 y1) = y0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := True /\ ((@IMAGE a0 a1 x0 x1) = x2).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a1 => (@IN a1 y0 (@UNIV a1)) -> exists y1 : a0, (@IN a0 y1 (@UNIV a0)) /\ ((x0 y1) = y0).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1) := True -> exists y0 : a0, (x0 y0) = x1.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (forall y2 : a1 -> Prop, (@SUBSET a1 y2 y1) -> exists y3 : a0 -> Prop, (@SUBSET a0 y3 y0) /\ ((@IMAGE a0 a1 x0 y3) = y2)) = (forall y2 : a1, (@IN a1 y2 y1) -> exists y3 : a0, (@IN a0 y3 y0) /\ ((x0 y3) = y2))) (@UNIV a0).
Definition term2 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (forall y3 : a1 -> Prop, (@SUBSET a1 y3 y2) -> exists y4 : a0 -> Prop, (@SUBSET a0 y4 y1) /\ ((@IMAGE a0 a1 y0 y4) = y3)) = (forall y3 : a1, (@IN a1 y3 y2) -> exists y4 : a0, (@IN a0 y4 y1) /\ ((y0 y4) = y3)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a1, (@IN a1 y0 (@UNIV a1)) -> exists y1 : a0, (@IN a0 y1 (@UNIV a0)) /\ ((x0 y1) = y0).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a1, exists y1 : a0, (x0 y1) = y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (forall y3 : a1 -> Prop, (@SUBSET a1 y3 y2) -> exists y4 : a0 -> Prop, (@SUBSET a0 y4 y1) /\ ((@IMAGE a0 a1 y0 y4) = y3)) = (forall y3 : a1, (@IN a1 y3 y2) -> exists y4 : a0, (@IN a0 y4 y1) /\ ((y0 y4) = y3))) x0.
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1) := fun y0 : a0 => (x0 y0) = x1.
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1) := exists y0 : a0, (x0 y0) = x1.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := imp (@SUBSET a0 x0 (@UNIV a0)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a1 -> Prop => (forall y1 : a1 -> Prop, (@SUBSET a1 y1 y0) -> exists y2 : a0 -> Prop, (@SUBSET a0 y2 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y2) = y1)) = (forall y1 : a1, (@IN a1 y1 y0) -> exists y2 : a0, (@IN a0 y2 (@UNIV a0)) /\ ((x0 y2) = y1))) (@UNIV a1).
Definition term42 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, (forall y1 : a1 -> Prop, exists y2 : a0 -> Prop, (@IMAGE a0 a1 y0 y2) = y1) = (forall y1 : a1, exists y2 : a0, (y0 y2) = y1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a1 -> Prop, (forall y1 : a1 -> Prop, (@SUBSET a1 y1 y0) -> exists y2 : a0 -> Prop, (@SUBSET a0 y2 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y2) = y1)) = (forall y1 : a1, (@IN a1 y1 y0) -> exists y2 : a0, (@IN a0 y2 (@UNIV a0)) /\ ((x0 y2) = y1)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) := exists y0 : a0 -> Prop, (@IMAGE a0 a1 x0 y0) = x1.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := @eq Prop (forall y0 : a1 -> Prop, exists y1 : a0 -> Prop, (@IMAGE a0 a1 x0 y1) = y0).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) := True -> exists y0 : a0 -> Prop, (@IMAGE a0 a1 x0 y0) = x1.
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a1 -> Prop => (@SUBSET a1 y0 (@UNIV a1)) -> exists y1 : a0 -> Prop, (@SUBSET a0 y1 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y1) = y0).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) := fun y0 : a0 -> Prop => (@IMAGE a0 a1 x0 y0) = x1.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) := (@SUBSET a1 x1 (@UNIV a1)) -> exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y0) = x1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1) := exists y0 : a0, (@IN a0 y0 (@UNIV a0)) /\ ((x0 y0) = x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a1 -> Prop, (@SUBSET a1 y0 (@UNIV a1)) -> exists y1 : a0 -> Prop, (@SUBSET a0 y1 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y1) = y0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => @SUBSET a0 y0 (@UNIV a0)) x0.
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a1) := (@IN a0 x1 (@UNIV a0)) /\ ((x0 x1) = x2).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (forall y2 : a1 -> Prop, (@SUBSET a1 y2 y1) -> exists y3 : a0 -> Prop, (@SUBSET a0 y3 y0) /\ ((@IMAGE a0 a1 x0 y3) = y2)) = (forall y2 : a1, (@IN a1 y2 y1) -> exists y3 : a0, (@IN a0 y3 y0) /\ ((x0 y3) = y2)).
Definition term25 (a0 : Type') (x0 : a0) := imp (@IN a0 x0 (@UNIV a0)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1 -> Prop) := fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y0) = x1).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := imp ((forall y0 : a1 -> Prop, exists y1 : a0 -> Prop, (@IMAGE a0 a1 x0 y1) = y0) = (forall y0 : a1, exists y1 : a0, (x0 y1) = y0)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := imp ((forall y0 : a1 -> Prop, (@SUBSET a1 y0 (@UNIV a1)) -> exists y1 : a0 -> Prop, (@SUBSET a0 y1 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y1) = y0)) = (forall y0 : a1, (@IN a1 y0 (@UNIV a1)) -> exists y1 : a0, (@IN a0 y1 (@UNIV a0)) /\ ((x0 y1) = y0))).
Definition term26 (a0 : Type') (x0 : a0) := and (@IN a0 x0 (@UNIV a0)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a1) := True /\ ((x0 x1) = x2).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a1) := (@IN a1 x1 (@UNIV a1)) -> exists y0 : a0, (@IN a0 y0 (@UNIV a0)) /\ ((x0 y0) = x1).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := @eq Prop (forall y0 : a1 -> Prop, (@SUBSET a1 y0 (@UNIV a1)) -> exists y1 : a0 -> Prop, (@SUBSET a0 y1 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 y1) = y0)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := (@SUBSET a0 x1 (@UNIV a0)) /\ ((@IMAGE a0 a1 x0 x1) = x2).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := and (@SUBSET a0 x0 (@UNIV a0)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a1 -> Prop, exists y1 : a0 -> Prop, (@IMAGE a0 a1 x0 y1) = y0.