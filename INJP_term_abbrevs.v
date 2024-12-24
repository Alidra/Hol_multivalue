Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (fun y0 : type1597 a0 => fun y1 : nat => fun y2 : a0 => @COND Prop (NUMLEFT y1) (x0 (NUMRIGHT y1) y2) (y0 (NUMRIGHT y1) y2)) x1.
Definition term8 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (fun y0 : type1597 a0 => (@INJP a0 x0 y0) = (fun y1 : nat => fun y2 : a0 => @COND Prop (NUMLEFT y1) (x0 (NUMRIGHT y1) y2) (y0 (NUMRIGHT y1) y2))) x1.
Definition term7 (a0 : Type') (x0 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, (@INJP a0 y0 y1) = (fun y2 : nat => fun y3 : a0 => @COND Prop (NUMLEFT y2) (y0 (NUMRIGHT y2) y3) (y1 (NUMRIGHT y2) y3))) x0.
Definition term1 (a0 : Type') (x0 : type1597 a0) := (fun y0 : type1597 a0 => fun y1 : type1597 a0 => fun y2 : nat => fun y3 : a0 => @COND Prop (NUMLEFT y2) (y0 (NUMRIGHT y2) y3) (y1 (NUMRIGHT y2) y3)) x0.
Definition term4 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := fun y0 : nat => fun y1 : a0 => @COND Prop (NUMLEFT y0) (x0 (NUMRIGHT y0) y1) (x1 (NUMRIGHT y0) y1).
Definition term2 (a0 : Type') (x0 : type1597 a0) := fun y0 : type1597 a0 => fun y1 : nat => fun y2 : a0 => @COND Prop (NUMLEFT y1) (x0 (NUMRIGHT y1) y2) (y0 (NUMRIGHT y1) y2).
Definition term0 (a0 : Type') := fun y0 : type1597 a0 => fun y1 : type1597 a0 => fun y2 : nat => fun y3 : a0 => @COND Prop (NUMLEFT y2) (y0 (NUMRIGHT y2) y3) (y1 (NUMRIGHT y2) y3).
Definition term6 (a0 : Type') := forall y0 : type1597 a0, forall y1 : type1597 a0, (@INJP a0 y0 y1) = (fun y2 : nat => fun y3 : a0 => @COND Prop (NUMLEFT y2) (y0 (NUMRIGHT y2) y3) (y1 (NUMRIGHT y2) y3)).
Definition term5 (a0 : Type') (x0 : type1597 a0) := forall y0 : type1597 a0, (@INJP a0 x0 y0) = (fun y1 : nat => fun y2 : a0 => @COND Prop (NUMLEFT y1) (x0 (NUMRIGHT y1) y2) (y0 (NUMRIGHT y1) y2)).
