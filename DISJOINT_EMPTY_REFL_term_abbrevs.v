Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 x0 x0)) = (@IN a0 y0 (@EMPTY a0)).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) /\ (@IN a0 x0 x1).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 x1 x1)).
Definition term24 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 x1).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 x0 x0)) = (@IN a0 y0 (@EMPTY a0)).
Definition term25 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 x1).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 x2).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (x0 = (@EMPTY a0)).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term8 (a0 : Type') := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) = (@IN a0 y1 (@EMPTY a0))) = (forall y1 : a0, (@IN a0 y1 (@INTER a0 y0 y0)) = (@IN a0 y1 (@EMPTY a0))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0)).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0))).
Definition term22 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0, ~ (x0 y0)).
Definition term5 (a0 : Type') := fun y0 : a0 -> Prop => (y0 = (@EMPTY a0)) = (@DISJOINT a0 y0 y0).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (@IN a0 x1 x2).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) = (@IN a0 y0 (@EMPTY a0)).
Definition term7 (a0 : Type') := forall y0 : a0 -> Prop, (y0 = (@EMPTY a0)) = (@DISJOINT a0 y0 y0).
Definition term6 (a0 : Type') := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) = (@IN a0 y1 (@EMPTY a0))) = (forall y1 : a0, (@IN a0 y1 (@INTER a0 y0 y0)) = (@IN a0 y1 (@EMPTY a0))).
Definition term23 (a0 : Type') := forall y0 : a0 -> Prop, True.
