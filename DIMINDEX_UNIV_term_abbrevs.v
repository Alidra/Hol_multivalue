Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') := fun y0 : a0 -> Prop => (@dimindex a0 y0) = (@dimindex a0 (@UNIV a0)).
Definition term3 (a0 : Type') := @eq nat (@COND nat (@FINITE a0 (@UNIV a0)) (@CARD a0 (@UNIV a0)) (NUMERAL (BIT1 0))).
Definition term8 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := @eq nat (@dimindex a0 x0).
Definition term9 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term1 (a0 : Type') := @COND nat (@FINITE a0 (@UNIV a0)) (@CARD a0 (@UNIV a0)) (NUMERAL (BIT1 0)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@dimindex a0 y0) = (@COND nat (@FINITE a0 (@UNIV a0)) (@CARD a0 (@UNIV a0)) (NUMERAL (BIT1 0)))) x0.
Definition term5 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term6 (a0 : Type') := forall y0 : a0 -> Prop, (@dimindex a0 y0) = (@dimindex a0 (@UNIV a0)).
Definition term7 (a0 : Type') := forall y0 : a0 -> Prop, True.
