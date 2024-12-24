Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (a0 : Type') (x0 : a0) (x1 : type1600 a0) := @INJP a0 (@INJA a0 x0) (@INJF a0 x1).
Definition term24 (a0 : Type') (x0 : nat) := @INJN a0 (S x0).
Definition term12 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) (x2 : type1597 a0) (x3 : type1597 a0) := (fun y0 : type1597 a0 => ((@INJP a0 x0 x2) = (@INJP a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0))) x3.
Definition term16 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1600 a0, (@ZCONSTR a0 x0 y0 y1) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 y0) (@INJF a0 y1)))) x1.
Definition term22 (a0 : Type') := @INJP a0 (@INJN a0 (NUMERAL 0)) (@ε (nat -> a0 -> Prop) (fun y0 : type1597 a0 => True)).
Definition term29 (a0 : Type') (x0 : a0) (x1 : type1600 a0) := False /\ ((@INJP a0 (@INJA a0 x0) (@INJF a0 x1)) = (@ε (nat -> a0 -> Prop) (fun y0 : type1597 a0 => True))).
Definition term23 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := ((@INJN a0 (S x0)) = (@INJN a0 (NUMERAL 0))) /\ ((@INJP a0 (@INJA a0 x1) (@INJF a0 x2)) = (@ε (nat -> a0 -> Prop) (fun y0 : type1597 a0 => True))).
Definition term19 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 x2)).
Definition term35 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term6 (a0 : Type') (x0 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, forall y2 : type1597 a0, forall y3 : type1597 a0, ((@INJP a0 y0 y2) = (@INJP a0 y1 y3)) = ((y0 = y1) /\ (y2 = y3))) x0.
Definition term27 (a0 : Type') := @ε (nat -> a0 -> Prop) (fun y0 : type1597 a0 => True).
Definition term4 (a0 : Type') (x0 : nat) := forall y0 : nat, ((@INJN a0 x0) = (@INJN a0 y0)) = (x0 = y0).
Definition term40 (a0 : Type') := forall y0 : a0, True.
Definition term18 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (fun y0 : type1600 a0 => (@ZCONSTR a0 x0 x1 y0) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 y0)))) x2.
Definition term7 (a0 : Type') (x0 : type1597 a0) := forall y0 : type1597 a0, forall y1 : type1597 a0, forall y2 : type1597 a0, ((@INJP a0 x0 y1) = (@INJP a0 y0 y2)) = ((x0 = y0) /\ (y1 = y2)).
Definition term41 (a0 : Type') := fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, ~ ((@ZCONSTR a0 y0 y1 y2) = (@ZBOT a0)).
Definition term14 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (@ZCONSTR a0 y0 y1 y2) = (@INJP a0 (@INJN a0 (S y0)) (@INJP a0 (@INJA a0 y1) (@INJF a0 y2)))) x0.
Definition term32 (a0 : Type') := fun y0 : type1600 a0 => True.
Definition term39 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1600 a0, ~ ((@ZCONSTR a0 x0 y0 y1) = (@ZBOT a0)).
Definition term11 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) (x2 : type1597 a0) := forall y0 : type1597 a0, ((@INJP a0 x0 x2) = (@INJP a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term13 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) (x2 : type1597 a0) (x3 : type1597 a0) := (x0 = x1) /\ (x2 = x3).
Definition term20 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @eq (nat -> a0 -> Prop) (@ZCONSTR a0 x0 x1 x2).
Definition term34 (a0 : Type') := forall y0 : type1600 a0, True.
Definition term43 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, ~ ((@ZCONSTR a0 y0 y1 y2) = (@ZBOT a0)).
Definition term31 (a0 : Type') (x0 : nat) (x1 : a0) := fun y0 : type1600 a0 => ~ ((@ZCONSTR a0 x0 x1 y0) = (@ZBOT a0)).
Definition term10 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) (x2 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, ((@INJP a0 x0 y0) = (@INJP a0 x1 y1)) = ((x0 = x1) /\ (y0 = y1))) x2.
Definition term38 (a0 : Type') := fun y0 : a0 => True.
Definition term44 := forall y0 : nat, True.
Definition term30 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := ~ ((@ZCONSTR a0 x0 x1 x2) = (@ZBOT a0)).
Definition term42 := fun y0 : nat => True.
Definition term1 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term17 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1600 a0, (@ZCONSTR a0 x0 x1 y0) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 y0))).
Definition term8 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, forall y2 : type1597 a0, ((@INJP a0 x0 y1) = (@INJP a0 y0 y2)) = ((x0 = y0) /\ (y1 = y2))) x1.
Definition term25 (a0 : Type') := @INJN a0 (NUMERAL 0).
Definition term9 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := forall y0 : type1597 a0, forall y1 : type1597 a0, ((@INJP a0 x0 y0) = (@INJP a0 x1 y1)) = ((x0 = x1) /\ (y0 = y1)).
Definition term28 (a0 : Type') (x0 : nat) := and ((@INJN a0 (S x0)) = (@INJN a0 (NUMERAL 0))).
Definition term3 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((@INJN a0 y0) = (@INJN a0 y1)) = (y0 = y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term36 (a0 : Type') (x0 : Prop) := forall y0 : type1600 a0, x0.
Definition term2 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term45 (x0 : Prop) := forall y0 : nat, x0.
Definition term33 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1600 a0, ~ ((@ZCONSTR a0 x0 x1 y0) = (@ZBOT a0)).
Definition term5 (a0 : Type') (x0 : nat) (x1 : nat) := (fun y0 : nat => ((@INJN a0 x0) = (@INJN a0 y0)) = (x0 = y0)) x1.
Definition term15 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1600 a0, (@ZCONSTR a0 x0 y0 y1) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 y0) (@INJF a0 y1))).
Definition term37 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : type1600 a0, ~ ((@ZCONSTR a0 x0 y0 y1) = (@ZBOT a0)).
Definition term21 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @eq (nat -> a0 -> Prop) (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 x2))).
