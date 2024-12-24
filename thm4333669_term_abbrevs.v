Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (a0 : Type') (a1 : Type') := False \/ ((@FINITE a0 (@UNIV a0)) /\ (@FINITE a1 (@UNIV a1))).
Definition term6 (a0 : Type') (a1 : Type') := @FINITE (prod a0 a1) (@CROSS a1 a0 (@UNIV a0) (@UNIV a1)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := @FINITE (prod a0 a1) (@CROSS a1 a0 x0 x1).
Definition term10 (a0 : Type') (a1 : Type') := ((@UNIV a1) = (@EMPTY a1)) \/ ((@FINITE a0 (@UNIV a0)) /\ (@FINITE a1 (@UNIV a1))).
Definition term0 (a0 : Type') := (~ ((@UNIV a0) = (@EMPTY a0))) -> ((@UNIV a0) = (@EMPTY a0)) = False.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 y0)) = ((x0 = (@EMPTY a0)) \/ ((y0 = (@EMPTY a1)) \/ ((@FINITE a0 x0) /\ (@FINITE a1 y0)))).
Definition term8 (a0 : Type') := or ((@UNIV a0) = (@EMPTY a0)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (@FINITE (prod a0 a1) (@CROSS a1 a0 y0 y1)) = ((y0 = (@EMPTY a0)) \/ ((y1 = (@EMPTY a1)) \/ ((@FINITE a0 y0) /\ (@FINITE a1 y1))))) x0.
Definition term9 (a0 : Type') (a1 : Type') := (@FINITE a0 (@UNIV a0)) /\ (@FINITE a1 (@UNIV a1)).
Definition term12 (a0 : Type') (a1 : Type') := @eq Prop (@FINITE (prod a0 a1) (@UNIV (prod a0 a1))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@FINITE (prod a0 a1) (@CROSS a1 a0 x0 y0)) = ((x0 = (@EMPTY a0)) \/ ((y0 = (@EMPTY a1)) \/ ((@FINITE a0 x0) /\ (@FINITE a1 y0))))) x1.
Definition term7 (a0 : Type') (a1 : Type') := ((@UNIV a0) = (@EMPTY a0)) \/ (((@UNIV a1) = (@EMPTY a1)) \/ ((@FINITE a0 (@UNIV a0)) /\ (@FINITE a1 (@UNIV a1)))).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (x0 = (@EMPTY a0)) \/ ((x1 = (@EMPTY a1)) \/ ((@FINITE a0 x0) /\ (@FINITE a1 x1))).
Definition term13 (a0 : Type') (a1 : Type') := @eq Prop ((@FINITE a0 (@UNIV a0)) /\ (@FINITE a1 (@UNIV a1))).
