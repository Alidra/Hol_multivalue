Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (x0 : a0) := fun y0 : a0 => (@IN a0 y0 (@DELETE a0 (@EMPTY a0) x0)) = (@IN a0 y0 (@EMPTY a0)).
Definition term10 (a0 : Type') (x0 : a0) := and (@IN a0 x0 (@EMPTY a0)).
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := False /\ (~ (x0 = x1)).
Definition term16 (a0 : Type') := forall y0 : a0, True.
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 y0 (@DELETE a0 (@EMPTY a0) x0)) = (@IN a0 y0 (@EMPTY a0)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@DELETE a0 x1 x2).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (@IN a0 x0 (@DELETE a0 (@EMPTY a0) x1)).
Definition term4 (a0 : Type') := forall y0 : a0, (@DELETE a0 (@EMPTY a0) y0) = (@EMPTY a0).
Definition term15 (a0 : Type') := fun y0 : a0 => True.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x2)).
Definition term3 (a0 : Type') := fun y0 : a0 => forall y1 : a0, (@IN a0 y1 (@DELETE a0 (@EMPTY a0) y0)) = (@IN a0 y1 (@EMPTY a0)).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) := (@IN a0 x0 (@EMPTY a0)) /\ (~ (x0 = x1)).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term5 (a0 : Type') := forall y0 : a0, forall y1 : a0, (@IN a0 y1 (@DELETE a0 (@EMPTY a0) y0)) = (@IN a0 y1 (@EMPTY a0)).
Definition term2 (a0 : Type') := fun y0 : a0 => (@DELETE a0 (@EMPTY a0) y0) = (@EMPTY a0).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@DELETE a0 (@EMPTY a0) x1).
