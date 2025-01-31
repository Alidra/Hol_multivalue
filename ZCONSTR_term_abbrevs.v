Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1600 a0, (@ZCONSTR a0 x0 y0 y1) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 y0) (@INJF a0 y1)))) x1.
Definition term6 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 x2)).
Definition term3 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => fun y1 : type1600 a0 => @INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 y0) (@INJF a0 y1))) x1.
Definition term12 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (fun y0 : type1600 a0 => (@ZCONSTR a0 x0 x1 y0) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 y0)))) x2.
Definition term1 (a0 : Type') (x0 : nat) := (fun y0 : nat => fun y1 : a0 => fun y2 : type1600 a0 => @INJP a0 (@INJN a0 (S y0)) (@INJP a0 (@INJA a0 y1) (@INJF a0 y2))) x0.
Definition term10 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (@ZCONSTR a0 y0 y1 y2) = (@INJP a0 (@INJN a0 (S y0)) (@INJP a0 (@INJA a0 y1) (@INJF a0 y2)))) x0.
Definition term9 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (@ZCONSTR a0 y0 y1 y2) = (@INJP a0 (@INJN a0 (S y0)) (@INJP a0 (@INJA a0 y1) (@INJF a0 y2))).
Definition term0 (a0 : Type') := fun y0 : nat => fun y1 : a0 => fun y2 : type1600 a0 => @INJP a0 (@INJN a0 (S y0)) (@INJP a0 (@INJA a0 y1) (@INJF a0 y2)).
Definition term7 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1600 a0, (@ZCONSTR a0 x0 x1 y0) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 y0))).
Definition term2 (a0 : Type') (x0 : nat) := fun y0 : a0 => fun y1 : type1600 a0 => @INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 y0) (@INJF a0 y1)).
Definition term4 (a0 : Type') (x0 : nat) (x1 : a0) := fun y0 : type1600 a0 => @INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 y0)).
Definition term8 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1600 a0, (@ZCONSTR a0 x0 y0 y1) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 y0) (@INJF a0 y1))).
Definition term5 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (fun y0 : type1600 a0 => @INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 y0))) x2.
