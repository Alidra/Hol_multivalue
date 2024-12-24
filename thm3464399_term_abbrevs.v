Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (a4 : Type') (a5 : Type') (a6 : Type') := (forall y0 : type1470 a1 a2, forall y1 : type1517 a0 a1 a2, (@INTERS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a2, exists y4 : a1, @SETSPEC (a0 -> Prop) y2 (y0 y3 y4) (y1 y3 y4)))) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (forall y4 : a2, forall y5 : a1, (y0 y4 y5) -> @IN a0 y3 (y1 y4 y5)) y3))) /\ (forall y0 : type1517 a4 a5 a6, forall y1 : type1524 a3 a4 a5 a6, (@INTERS a3 (@GSPEC (a3 -> Prop) (fun y2 : a3 -> Prop => exists y3 : a6, exists y4 : a5, exists y5 : a4, @SETSPEC (a3 -> Prop) y2 (y0 y3 y4 y5) (y1 y3 y4 y5)))) = (@GSPEC a3 (fun y2 : a3 => exists y3 : a3, @SETSPEC a3 y2 (forall y4 : a6, forall y5 : a5, forall y6 : a4, (y0 y4 y5 y6) -> @IN a3 y3 (y1 y4 y5 y6)) y3))).
