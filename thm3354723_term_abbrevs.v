Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := @INTERS a0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTERS a0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))))) = (@IN a0 y0 x0).