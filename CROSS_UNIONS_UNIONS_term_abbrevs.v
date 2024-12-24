Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : type686 a0, forall y1 : type686 a1, (@CROSS a1 a0 (@UNIONS a0 y0) (@UNIONS a1 y1)) = (@UNIONS (prod a0 a1) (@GSPEC ((prod a0 a1) -> Prop) (fun y2 : type1210 a0 a1 => exists y3 : a0 -> Prop, exists y4 : a1 -> Prop, @SETSPEC ((prod a0 a1) -> Prop) y2 ((@IN (a0 -> Prop) y3 y0) /\ (@IN (a1 -> Prop) y4 y1)) (@CROSS a1 a0 y3 y4)))).
