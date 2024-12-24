Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)) -> ((@CARD a0 x0) = x1) = True.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)) -> ((@CARD a0 x0) = x1) = True) -> ((@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1) = (((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)) -> True).
Definition term23 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : Prop) := ((@HAS_SIZE a0 x0 x1) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1))) -> (((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)) -> ((@CARD a0 x0) = x1) = x2) -> ((@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1) = (((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)) -> x2).
Definition term29 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => (@HAS_SIZE a0 x0 y0) -> (@CARD a0 x0) = y0.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := @eq nat (@CARD a0 x0).
Definition term25 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) -> (@CARD a0 y0) = y1.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((@HAS_SIZE a0 x0 x1) = x2) -> (x2 -> ((@CARD a0 x0) = x1) = y0) -> ((@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1) = (x2 -> y0)) x3.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((@HAS_SIZE a0 x0 x1) = x2) -> (x2 -> ((@CARD a0 x0) = x1) = x3) -> ((@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1) = (x2 -> x3).
Definition term22 := forall y0 : nat, True.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term20 := fun y0 : nat => True.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)) -> True.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((@HAS_SIZE a0 x0 x1) = x2) -> (x2 -> ((@CARD a0 x0) = x1) = y0) -> ((@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1) = (x2 -> y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term26 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((@HAS_SIZE a0 x0 x1) = y0) -> (y0 -> ((@CARD a0 x0) = x1) = y1) -> ((@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1) = (y0 -> y1).
Definition term6 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term27 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) -> (@CARD a0 y0) = y1.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) -> (@CARD a0 x0) = y0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term24 (x0 : Prop) := forall y0 : nat, x0.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : Prop) := (((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)) -> ((@CARD a0 x0) = x1) = x2) -> ((@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1) = (((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)) -> x2).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@HAS_SIZE a0 x0 x1) = y0) -> (y0 -> ((@CARD a0 x0) = x1) = y1) -> ((@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1) = (y0 -> y1)) x2.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1.
Definition term28 (a0 : Type') := forall y0 : a0 -> Prop, True.
