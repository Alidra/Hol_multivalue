Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> Prop) := ((x0 = (@EMPTY (a1 -> Prop))) -> (@CROSS a1 a0 x1 (@INTERS a1 x0)) = (@CROSS a1 a0 x1 (@UNIV a1))) /\ ((~ (x0 = (@EMPTY (a1 -> Prop)))) -> (@CROSS a1 a0 x1 (@INTERS a1 x0)) = (@INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y0 : type1210 a0 a1 => exists y1 : a1 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y0 (@IN (a1 -> Prop) y1 x0) (@CROSS a1 a0 x1 y1))))).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) := @CROSS a1 a0 x0 (@INTERS a1 x1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> Prop) := @INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y0 : type1210 a0 a1 => exists y1 : a1 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y0 (@IN (a1 -> Prop) y1 x0) (@CROSS a1 a0 x1 y1))).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> Prop) := @COND ((prod a0 a1) -> Prop) (x0 = (@EMPTY (a1 -> Prop))) (@CROSS a1 a0 x1 (@UNIV a1)) (@INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y0 : type1210 a0 a1 => exists y1 : a1 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y0 (@IN (a1 -> Prop) y1 x0) (@CROSS a1 a0 x1 y1)))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> Prop) := (x0 = (@EMPTY (a1 -> Prop))) -> (@CROSS a1 a0 x1 (@INTERS a1 x0)) = (@CROSS a1 a0 x1 (@UNIV a1)).
Definition term0 (a0 : Type') (x0 : type686 a0) := ~ (x0 = (@EMPTY (a0 -> Prop))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> Prop) := (~ (x0 = (@EMPTY (a1 -> Prop)))) -> (@CROSS a1 a0 x1 (@INTERS a1 x0)) = (@INTERS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y0 : type1210 a0 a1 => exists y1 : a1 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y0 (@IN (a1 -> Prop) y1 x0) (@CROSS a1 a0 x1 y1)))).
