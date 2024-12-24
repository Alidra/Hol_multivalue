Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term2 (a0 : Type') := ~ ((@UNIV a0) = (@EMPTY a0)).
Definition term4 (a0 : Type') (x0 : a0) := @eq Prop (@IN a0 x0 (@UNIV a0)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term3 (a0 : Type') := ~ (forall y0 : a0, (@IN a0 y0 (@UNIV a0)) = (@IN a0 y0 (@EMPTY a0))).
Definition term7 (a0 : Type') := forall y0 : a0, False.
Definition term5 (a0 : Type') := fun y0 : a0 => (@IN a0 y0 (@UNIV a0)) = (@IN a0 y0 (@EMPTY a0)).
Definition term6 (a0 : Type') := fun y0 : a0 => False.
Definition term1 (a0 : Type') := forall y0 : a0, (@IN a0 y0 (@UNIV a0)) = (@IN a0 y0 (@EMPTY a0)).
