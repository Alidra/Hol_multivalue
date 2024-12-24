Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : type686 a1, (@CROSS a1 a0 y0 (@INTERS a1 y1)) = (@COND ((prod a0 a1) -> Prop) (y1 = (@EMPTY (a1 -> Prop))) (@CROSS a1 a0 y0 (@UNIV a1)) (@INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y2 : type1210 a0 a1 => exists y3 : a1 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y2 (@IN (a1 -> Prop) y3 y1) (@CROSS a1 a0 y0 y3))))).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : type686 a1, (@CROSS a1 a0 x0 (@INTERS a1 y0)) = (@COND ((prod a0 a1) -> Prop) (y0 = (@EMPTY (a1 -> Prop))) (@CROSS a1 a0 x0 (@UNIV a1)) (@INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y1 : type1210 a0 a1 => exists y2 : a1 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y1 (@IN (a1 -> Prop) y2 y0) (@CROSS a1 a0 x0 y2))))).
