Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) = (@HAS_SIZE a0 y0 (@CARD a0 y0)).
Definition term14 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (@FINITE a0 x0).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = (@CARD a0 x0)).
Definition term9 (a0 : Type') := fun y0 : a0 -> Prop => (@FINITE a0 y0) = (@HAS_SIZE a0 y0 (@CARD a0 y0)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term10 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) /\ True.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := @HAS_SIZE a0 x0 (@CARD a0 x0).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, True.
