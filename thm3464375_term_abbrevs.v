Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := forall y0 : a0, (@IN a0 y0 (@INTERS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a1, @SETSPEC (a0 -> Prop) y1 (x0 y2) (x1 y2))))) = (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a1, (x0 y3) -> @IN a0 y2 (x1 y3)) y2))).
