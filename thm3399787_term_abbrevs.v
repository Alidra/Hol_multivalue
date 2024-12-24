Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term1 (a0 : Type') := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 True y1).
Definition term2 (a0 : Type') := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 True y2))) = (@IN a0 y0 (@UNIV a0)).
