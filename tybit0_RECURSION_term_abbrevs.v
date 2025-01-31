Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := fun y0 : type46 a0 => exists y1 : type1344 a0 a1, forall y2 : finite_sum a0 a0, (y1 (y0 y2)) = (x0 y2).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := @eq Prop (exists y0 : type1344 a0 a1, forall y1 : finite_sum a0 a0, (y0 (@_103783 a0 y1)) = (x0 y1)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := @eq Prop ((fun y0 : type46 a0 => exists y1 : type1344 a0 a1, forall y2 : finite_sum a0 a0, (y1 (y0 y2)) = (x0 y2)) (@_103783 a0)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := exists y0 : type1344 a0 a1, forall y1 : finite_sum a0 a0, (y0 (@mktybit0 a0 y1)) = (x0 y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := exists y0 : type1344 a0 a1, forall y1 : finite_sum a0 a0, (y0 (@_103783 a0 y1)) = (x0 y1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := (fun y0 : type46 a0 => exists y1 : type1344 a0 a1, forall y2 : finite_sum a0 a0, (y1 (y0 y2)) = (x0 y2)) (@mktybit0 a0).
Definition term8 (a0 : Type') (a1 : Type') := forall y0 : type47 a0 a1, exists y1 : type1344 a0 a1, forall y2 : finite_sum a0 a0, (y1 (@mktybit0 a0 y2)) = (y0 y2).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := (fun y0 : type47 a0 a1 => exists y1 : type1344 a0 a1, forall y2 : finite_sum a0 a0, (y1 (@_103783 a0 y2)) = (y0 y2)) x0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type47 a0 a1) := (fun y0 : type46 a0 => exists y1 : type1344 a0 a1, forall y2 : finite_sum a0 a0, (y1 (y0 y2)) = (x0 y2)) (@_103783 a0).
