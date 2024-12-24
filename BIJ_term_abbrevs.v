Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => fun y1 : a0 -> Prop => fun y2 : a1 -> Prop => (@INJ a0 a1 y0 y1 y2) /\ (@SURJ a0 a1 y0 y1 y2)) x0.
Definition term9 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (@BIJ a0 a1 y0 y1 y2) = ((@INJ a0 a1 y0 y1 y2) /\ (@SURJ a0 a1 y0 y1 y2)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : a1 -> Prop => (@INJ a0 a1 x0 x1 y0) /\ (@SURJ a0 a1 x0 x1 y0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (@BIJ a0 a1 y0 y1 y2) = ((@INJ a0 a1 y0 y1 y2) /\ (@SURJ a0 a1 y0 y1 y2))) x0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (@BIJ a0 a1 x0 y0 y1) = ((@INJ a0 a1 x0 y0 y1) /\ (@SURJ a0 a1 x0 y0 y1))) x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> Prop => fun y1 : a1 -> Prop => (@INJ a0 a1 x0 y0 y1) /\ (@SURJ a0 a1 x0 y0 y1).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := forall y0 : a1 -> Prop, (@BIJ a0 a1 x0 x1 y0) = ((@INJ a0 a1 x0 x1 y0) /\ (@SURJ a0 a1 x0 x1 y0)).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => fun y1 : a0 -> Prop => fun y2 : a1 -> Prop => (@INJ a0 a1 y0 y1 y2) /\ (@SURJ a0 a1 y0 y1 y2).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (@BIJ a0 a1 x0 y0 y1) = ((@INJ a0 a1 x0 y0 y1) /\ (@SURJ a0 a1 x0 y0 y1)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@BIJ a0 a1 x0 x1 y0) = ((@INJ a0 a1 x0 x1 y0) /\ (@SURJ a0 a1 x0 x1 y0))) x2.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@INJ a0 a1 x0 x1 y0) /\ (@SURJ a0 a1 x0 x1 y0)) x2.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := (@INJ a0 a1 x0 x1 x2) /\ (@SURJ a0 a1 x0 x1 x2).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a1 -> Prop => (@INJ a0 a1 x0 y0 y1) /\ (@SURJ a0 a1 x0 y0 y1)) x1.
