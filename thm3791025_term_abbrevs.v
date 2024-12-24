Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) (x2 : nat) (x3 : a1) (x4 : type1411 a0 a1) := (fun y0 : type1411 a0 a1 => (@FINREC a0 a1 y0 x0 x1 x3 (S x2)) = (exists y1 : a0, exists y2 : a1, (@IN a0 y1 x1) /\ ((@FINREC a0 a1 y0 x0 (@DELETE a0 x1 y1) y2 x2) /\ (x3 = (y0 y1 y2))))) x4.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) (x2 : a0 -> Prop) (x3 : a1) (x4 : nat) := @FINREC a0 a1 x0 x1 x2 x3 (S x4).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) (x2 : nat) (x3 : a1) (x4 : type1411 a0 a1) := exists y0 : a0, exists y1 : a1, (@IN a0 y0 x1) /\ ((@FINREC a0 a1 x4 x0 (@DELETE a0 x1 y0) y1 x2) /\ (x3 = (x4 y0 y1))).
