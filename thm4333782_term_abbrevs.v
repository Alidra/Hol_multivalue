Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') := or (@INFINITE a0 (@UNIV a0)).
Definition term11 (a0 : Type') := True /\ (@INFINITE a0 (@UNIV a0)).
Definition term20 (a0 : Type') (a1 : Type') := (@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1)).
Definition term17 (a0 : Type') (a1 : Type') := (@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0)).
Definition term8 (a0 : Type') := ~ ((@UNIV a0) = (@EMPTY a0)).
Definition term16 (a0 : Type') := (@INFINITE a0 (@UNIV a0)) /\ True.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := ((~ (x0 = (@EMPTY a0))) /\ (@INFINITE a1 x1)) \/ ((@INFINITE a0 x0) /\ (~ (x1 = (@EMPTY a1)))).
Definition term0 (a0 : Type') := (~ ((@UNIV a0) = (@EMPTY a0))) -> ((@UNIV a0) = (@EMPTY a0)) = False.
Definition term6 (a0 : Type') (a1 : Type') := @INFINITE (prod a0 a1) (@CROSS a1 a0 (@UNIV a0) (@UNIV a1)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, (@INFINITE (prod a0 a1) (@CROSS a1 a0 x0 y0)) = (((~ (x0 = (@EMPTY a0))) /\ (@INFINITE a1 y0)) \/ ((@INFINITE a0 x0) /\ (~ (y0 = (@EMPTY a1))))).
Definition term12 (a0 : Type') (a1 : Type') := or ((~ ((@UNIV a0) = (@EMPTY a0))) /\ (@INFINITE a1 (@UNIV a1))).
Definition term10 (a0 : Type') (a1 : Type') := (~ ((@UNIV a0) = (@EMPTY a0))) /\ (@INFINITE a1 (@UNIV a1)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (@INFINITE (prod a0 a1) (@CROSS a1 a0 y0 y1)) = (((~ (y0 = (@EMPTY a0))) /\ (@INFINITE a1 y1)) \/ ((@INFINITE a0 y0) /\ (~ (y1 = (@EMPTY a1)))))) x0.
Definition term14 (a0 : Type') := and (@INFINITE a0 (@UNIV a0)).
Definition term15 (a0 : Type') (a1 : Type') := (@INFINITE a0 (@UNIV a0)) /\ (~ ((@UNIV a1) = (@EMPTY a1))).
Definition term18 (a0 : Type') (a1 : Type') := @eq Prop (@INFINITE (prod a0 a1) (@UNIV (prod a0 a1))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@INFINITE (prod a0 a1) (@CROSS a1 a0 x0 y0)) = (((~ (x0 = (@EMPTY a0))) /\ (@INFINITE a1 y0)) \/ ((@INFINITE a0 x0) /\ (~ (y0 = (@EMPTY a1)))))) x1.
Definition term7 (a0 : Type') (a1 : Type') := ((~ ((@UNIV a0) = (@EMPTY a0))) /\ (@INFINITE a1 (@UNIV a1))) \/ ((@INFINITE a0 (@UNIV a0)) /\ (~ ((@UNIV a1) = (@EMPTY a1)))).
Definition term19 (a0 : Type') (a1 : Type') := @eq Prop ((@INFINITE a1 (@UNIV a1)) \/ (@INFINITE a0 (@UNIV a0))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := @INFINITE (prod a0 a1) (@CROSS a1 a0 x0 x1).
Definition term9 (a0 : Type') := and (~ ((@UNIV a0) = (@EMPTY a0))).
