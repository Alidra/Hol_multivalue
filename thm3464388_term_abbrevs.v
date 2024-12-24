Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (x0 : type1517 a1 a2 a3) := forall y0 : type1524 a0 a1 a2 a3, (@INTERS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a3, exists y3 : a2, exists y4 : a1, @SETSPEC (a0 -> Prop) y1 (x0 y2 y3 y4) (y0 y2 y3 y4)))) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a3, forall y4 : a2, forall y5 : a1, (x0 y3 y4 y5) -> @IN a0 y2 (y0 y3 y4 y5)) y2)).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') := forall y0 : type1517 a1 a2 a3, forall y1 : type1524 a0 a1 a2 a3, (@INTERS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a3, exists y4 : a2, exists y5 : a1, @SETSPEC (a0 -> Prop) y2 (y0 y3 y4 y5) (y1 y3 y4 y5)))) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (forall y4 : a3, forall y5 : a2, forall y6 : a1, (y0 y4 y5 y6) -> @IN a0 y3 (y1 y4 y5 y6)) y3)).
