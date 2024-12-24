Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (~ (x0 = x1)).
Definition term8 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> @IN a0 x0 x1.
Definition term7 (a0 : Type') := forall y0 : a0, True.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x0.
Definition term16 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term14 (a0 : Type') := forall y0 : a0 -> Prop, ~ (@PSUBSET a0 y0 y0).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 x0.
Definition term6 (a0 : Type') := fun y0 : a0 => True.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := ~ (x0 = x0).
Definition term13 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term12 (a0 : Type') := fun y0 : a0 -> Prop => ~ (@PSUBSET a0 y0 y0).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := ~ (@PSUBSET a0 x0 x0).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (@SUBSET a0 x0 x0) /\ (~ (x0 = x0)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := and (@SUBSET a0 x0 x0).
Definition term15 (a0 : Type') := forall y0 : a0 -> Prop, True.
