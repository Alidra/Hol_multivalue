Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => forall y1 : a0, (@IN a0 y1 (@UNIONS a0 y0)) = (exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) /\ (@IN a0 y1 y2))) x0.
Definition term2 (a0 : Type') (x0 : type686 a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@UNIONS a0 x0)) = (exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ (@IN a0 y0 y1))) x1.
Definition term1 (a0 : Type') (x0 : type686 a0) := forall y0 : a0, (@IN a0 y0 (@UNIONS a0 x0)) = (exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ (@IN a0 y0 y1)).
