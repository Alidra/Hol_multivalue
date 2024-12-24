Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term1 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term0 (a0 : Type') (x0 : type686 a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@INTERS a0 x0)) = (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) -> @IN a0 y0 y1)) x1.
