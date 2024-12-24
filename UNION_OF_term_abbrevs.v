Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (fun y0 : type686 a0 => fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> y0 y3) /\ ((@UNIONS a0 y2) = y1))) x1.
Definition term5 (a0 : Type') (x0 : type180 a0) := forall y0 : type686 a0, (@UNION_OF a0 x0 y0) = (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> y0 y3) /\ ((@UNIONS a0 y2) = y1))).
Definition term1 (a0 : Type') (x0 : type180 a0) := (fun y0 : type180 a0 => fun y1 : type686 a0 => fun y2 : a0 -> Prop => exists y3 : type686 a0, (y0 y3) /\ ((forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y3) -> y1 y4) /\ ((@UNIONS a0 y3) = y2))) x0.
Definition term7 (a0 : Type') (x0 : type180 a0) := (fun y0 : type180 a0 => forall y1 : type686 a0, (@UNION_OF a0 y0 y1) = (fun y2 : a0 -> Prop => exists y3 : type686 a0, (y0 y3) /\ ((forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y3) -> y1 y4) /\ ((@UNIONS a0 y3) = y2)))) x0.
Definition term0 (a0 : Type') := fun y0 : type180 a0 => fun y1 : type686 a0 => fun y2 : a0 -> Prop => exists y3 : type686 a0, (y0 y3) /\ ((forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y3) -> y1 y4) /\ ((@UNIONS a0 y3) = y2)).
Definition term2 (a0 : Type') (x0 : type180 a0) := fun y0 : type686 a0 => fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> y0 y3) /\ ((@UNIONS a0 y2) = y1)).
Definition term4 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => exists y1 : type686 a0, (x0 y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> x1 y2) /\ ((@UNIONS a0 y1) = y0)).
Definition term6 (a0 : Type') := forall y0 : type180 a0, forall y1 : type686 a0, (@UNION_OF a0 y0 y1) = (fun y2 : a0 -> Prop => exists y3 : type686 a0, (y0 y3) /\ ((forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y3) -> y1 y4) /\ ((@UNIONS a0 y3) = y2))).
Definition term8 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (fun y0 : type686 a0 => (@UNION_OF a0 x0 y0) = (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> y0 y3) /\ ((@UNIONS a0 y2) = y1)))) x1.
