Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0).
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term0 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@UNIONS a0 x1).
Definition term8 (a0 : Type') := fun y0 : a0 -> Prop => False.
Definition term16 (a0 : Type') := forall y0 : a0, True.
Definition term15 (a0 : Type') := forall y0 : a0, (@IN a0 y0 (@UNIONS a0 (@EMPTY (a0 -> Prop)))) = (@IN a0 y0 (@EMPTY a0)).
Definition term11 (a0 : Type') (x0 : Prop) := exists y0 : a0 -> Prop, x0.
Definition term3 (a0 : Type') (x0 : a0) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) /\ (@IN a0 x0 y0).
Definition term9 (a0 : Type') := exists y0 : a0 -> Prop, False.
Definition term2 (a0 : Type') (x0 : a0) := @IN a0 x0 (@UNIONS a0 (@EMPTY (a0 -> Prop))).
Definition term14 (a0 : Type') := fun y0 : a0 => True.
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN (a0 -> Prop) x1 (@EMPTY (a0 -> Prop))) /\ (@IN a0 x0 x1).
Definition term7 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) /\ (@IN a0 x0 y0).
Definition term10 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := False /\ (x0 x1).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := and (@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term12 (a0 : Type') (x0 : a0) := @eq Prop (@IN a0 x0 (@UNIONS a0 (@EMPTY (a0 -> Prop)))).
Definition term13 (a0 : Type') := fun y0 : a0 => (@IN a0 y0 (@UNIONS a0 (@EMPTY (a0 -> Prop)))) = (@IN a0 y0 (@EMPTY a0)).
