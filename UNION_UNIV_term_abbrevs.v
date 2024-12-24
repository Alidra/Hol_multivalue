Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := True \/ (x0 x1).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) \/ (@IN a0 x1 (@UNIV a0)).
Definition term25 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term24 (a0 : Type') := forall y0 : a0, True.
Definition term28 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@UNION a0 (@UNIV a0) x1)).
Definition term14 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@UNION a0 (@UNIV a0) y0)) = (@IN a0 y1 (@UNIV a0))) /\ (forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@UNION a0 y0 (@UNIV a0))) = (@IN a0 y1 (@UNIV a0))).
Definition term9 (a0 : Type') := fun y0 : a0 -> Prop => (@UNION a0 y0 (@UNIV a0)) = (@UNIV a0).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term2 (a0 : Type') := fun y0 : a0 -> Prop => (@UNION a0 (@UNIV a0) y0) = (@UNIV a0).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@UNION a0 (@UNIV a0) x1).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 (@UNIV a0)).
Definition term10 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@UNION a0 y0 (@UNIV a0))) = (@IN a0 y1 (@UNIV a0)).
Definition term3 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@UNION a0 (@UNIV a0) y0)) = (@IN a0 y1 (@UNIV a0)).
Definition term7 (a0 : Type') := and (forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@UNION a0 (@UNIV a0) y0)) = (@IN a0 y1 (@UNIV a0))).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) \/ True.
Definition term23 (a0 : Type') := fun y0 : a0 => True.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 x0 (@UNIV a0))) = (@IN a0 y0 (@UNIV a0)).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 (@UNIV a0) x0)) = (@IN a0 y0 (@UNIV a0)).
Definition term26 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 (@UNIV a0)) \/ (@IN a0 x0 x1).
Definition term4 (a0 : Type') := forall y0 : a0 -> Prop, (@UNION a0 (@UNIV a0) y0) = (@UNIV a0).
Definition term19 (a0 : Type') (x0 : a0) := or (@IN a0 x0 (@UNIV a0)).
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, (@UNION a0 y0 (@UNIV a0)) = (@UNIV a0).
Definition term13 (a0 : Type') := (forall y0 : a0 -> Prop, (@UNION a0 (@UNIV a0) y0) = (@UNIV a0)) /\ (forall y0 : a0 -> Prop, (@UNION a0 y0 (@UNIV a0)) = (@UNIV a0)).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@UNION a0 x1 (@UNIV a0))).
Definition term6 (a0 : Type') := and (forall y0 : a0 -> Prop, (@UNION a0 (@UNIV a0) y0) = (@UNIV a0)).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@UNION a0 y0 (@UNIV a0))) = (@IN a0 y1 (@UNIV a0)).
Definition term5 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@UNION a0 (@UNIV a0) y0)) = (@IN a0 y1 (@UNIV a0)).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term27 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 x0 (@UNIV a0))) = (@IN a0 y0 (@UNIV a0)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 (@UNIV a0) x0)) = (@IN a0 y0 (@UNIV a0)).
