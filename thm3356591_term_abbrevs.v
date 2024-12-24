Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := forall y0 : a0, (@IN a0 y0 (@INTERS a0 (@INSERT (a0 -> Prop) x0 x1))) = (@IN a0 y0 (@INTER a0 x0 (@INTERS a0 x1))).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @INTER a0 x0 (@INTERS a0 x1).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @INTERS a0 (@INSERT (a0 -> Prop) x0 x1).
