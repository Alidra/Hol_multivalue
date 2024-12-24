Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type686 a0) := forall y0 : a1 -> Prop, (@CROSS a1 a0 (@INTERS a0 x0) y0) = (@COND ((prod a0 a1) -> Prop) (x0 = (@EMPTY (a0 -> Prop))) (@CROSS a1 a0 (@UNIV a0) y0) (@INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y1 : type1210 a0 a1 => exists y2 : a0 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y1 (@IN (a0 -> Prop) y2 x0) (@CROSS a1 a0 y2 y0))))).
Definition term1 (a0 : Type') (a1 : Type') := forall y0 : type686 a0, forall y1 : a1 -> Prop, (@CROSS a1 a0 (@INTERS a0 y0) y1) = (@COND ((prod a0 a1) -> Prop) (y0 = (@EMPTY (a0 -> Prop))) (@CROSS a1 a0 (@UNIV a0) y1) (@INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y2 : type1210 a0 a1 => exists y3 : a0 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y2 (@IN (a0 -> Prop) y3 y0) (@CROSS a1 a0 y3 y1))))).
