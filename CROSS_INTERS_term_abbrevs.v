Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') := (forall y0 : a0 -> Prop, forall y1 : type686 a1, (@CROSS a1 a0 y0 (@INTERS a1 y1)) = (@COND ((prod a0 a1) -> Prop) (y1 = (@EMPTY (a1 -> Prop))) (@CROSS a1 a0 y0 (@UNIV a1)) (@INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y2 : type1210 a0 a1 => exists y3 : a1 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y2 (@IN (a1 -> Prop) y3 y1) (@CROSS a1 a0 y0 y3)))))) /\ (forall y0 : type686 a2, forall y1 : a3 -> Prop, (@CROSS a3 a2 (@INTERS a2 y0) y1) = (@COND ((prod a2 a3) -> Prop) (y0 = (@EMPTY (a2 -> Prop))) (@CROSS a3 a2 (@UNIV a2) y1) (@INTERS (prod a2 a3) (@GSPEC ((prod a2 a3) -> Prop) (fun y2 : type1210 a2 a3 => exists y3 : a2 -> Prop, @SETSPEC ((prod a2 a3) -> Prop) y2 (@IN (a2 -> Prop) y3 y0) (@CROSS a3 a2 y3 y1)))))).
