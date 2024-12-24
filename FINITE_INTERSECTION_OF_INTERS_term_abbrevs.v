Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 (@INTERS a0 x1).
Definition term24 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := exists y0 : type686 a0, (@FINITE (a0 -> Prop) y0) /\ ((forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y1) /\ ((@INTERS a0 y0) = (@INTERS a0 x1))).
Definition term10 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (@FINITE (a0 -> Prop) x0) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x1 y0).
Definition term18 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : type686 a0, (@FINITE (a0 -> Prop) y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y3) /\ ((@INTERS a0 y2) = y1))) y0) (@INTERS a0 x1).
Definition term25 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x1 y0) x2.
Definition term31 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term21 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : type686 a0, (@FINITE (a0 -> Prop) y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y3) /\ ((@INTERS a0 y2) = y1))) y0.
Definition term19 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => exists y1 : type686 a0, (@FINITE (a0 -> Prop) y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y2) /\ ((@INTERS a0 y1) = y0))) x1.
Definition term17 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => x0 y0) x1.
Definition term20 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : type686 a0, (@FINITE (a0 -> Prop) y0) /\ ((forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y1) /\ ((@INTERS a0 y0) = x1)).
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term22 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @eq Prop ((fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : type686 a0, (@FINITE (a0 -> Prop) y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y3) /\ ((@INTERS a0 y2) = y1))) y0) (@INTERS a0 x1)).
Definition term33 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := and (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x1 y0).
Definition term6 (a0 : Type') := fun y0 : type686 a0 => (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0) = (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0)).
Definition term1 (a0 : Type') (x0 : type180 a0) := forall y0 : type686 a0, (@INTERSECTION_OF a0 x0 y0) = (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> y0 y3) /\ ((@INTERS a0 y2) = y1))).
Definition term5 (a0 : Type') := fun y0 : type686 a0 => (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0)) = (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0).
Definition term23 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @eq Prop ((fun y0 : a0 -> Prop => exists y1 : type686 a0, (@FINITE (a0 -> Prop) y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y2) /\ ((@INTERS a0 y1) = y0))) (@INTERS a0 x1)).
Definition term37 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := ((@FINITE (a0 -> Prop) x1) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y0)) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 (@INTERS a0 x1).
Definition term0 (a0 : Type') (x0 : type180 a0) := (fun y0 : type180 a0 => forall y1 : type686 a0, (@INTERSECTION_OF a0 y0 y1) = (fun y2 : a0 -> Prop => exists y3 : type686 a0, (y0 y3) /\ ((forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y3) -> y1 y4) /\ ((@INTERS a0 y3) = y2)))) x0.
Definition term13 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0) (@INTERS a0 x1).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term8 (a0 : Type') := forall y0 : type686 a0, (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0) = (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0)).
Definition term29 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term7 (a0 : Type') := forall y0 : type686 a0, (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0)) = (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0).
Definition term39 (a0 : Type') := forall y0 : type686 a0, forall y1 : type686 a0, ((@FINITE (a0 -> Prop) y1) /\ (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0 y2)) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0 (@INTERS a0 y1).
Definition term4 (a0 : Type') (x0 : type686 a0) := @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0).
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x1 x2.
Definition term15 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (fun y0 : a0 -> Prop => exists y1 : type686 a0, (@FINITE (a0 -> Prop) y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y2) /\ ((@INTERS a0 y1) = y0))) (@INTERS a0 x1).
Definition term38 (a0 : Type') (x0 : type686 a0) := forall y0 : type686 a0, ((@FINITE (a0 -> Prop) y0) /\ (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y1)) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 (@INTERS a0 y0).
Definition term11 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x1 y0.
Definition term36 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : type686 a0 => (@FINITE (a0 -> Prop) y0) /\ ((forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y1) /\ ((@INTERS a0 y0) = (@INTERS a0 x1))).
Definition term35 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (@FINITE (a0 -> Prop) x1) /\ ((forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y0) /\ ((@INTERS a0 x1) = (@INTERS a0 x1))).
Definition term9 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0) = (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0))) x0.
Definition term27 (a0 : Type') (x0 : type686 a0) := and (@FINITE (a0 -> Prop) x0).
Definition term14 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => exists y1 : type686 a0, (@FINITE (a0 -> Prop) y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y2) /\ ((@INTERS a0 y1) = y0)).
Definition term3 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => exists y1 : type686 a0, (x0 y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> x1 y2) /\ ((@INTERS a0 y1) = y0)).
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x1 y0.
Definition term2 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (fun y0 : type686 a0 => (@INTERSECTION_OF a0 x0 y0) = (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> y0 y3) /\ ((@INTERS a0 y2) = y1)))) x1.
Definition term34 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y0) /\ ((@INTERS a0 x1) = (@INTERS a0 x1)).
Definition term30 (a0 : Type') := forall y0 : a0 -> Prop, True.
