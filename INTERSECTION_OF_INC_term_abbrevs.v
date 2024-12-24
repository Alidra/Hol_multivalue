Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := (x2 = x0) -> (x1 x2) = True.
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term43 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop)))) -> x0 y0) /\ ((@INTERS a0 (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop)))) = x1).
Definition term12 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> x1 y3) /\ ((@INTERS a0 y2) = y1))) y0) x2).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0)) x1.
Definition term11 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> x1 y3) /\ ((@INTERS a0 y2) = y1))) y0.
Definition term44 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ ((forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) -> x1 y0) /\ ((@INTERS a0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) = x2)).
Definition term8 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => x0 y0) x1.
Definition term6 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => exists y1 : type686 a0, (x0 y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> x1 y2) /\ ((@INTERS a0 y1) = y0))) x2.
Definition term45 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := fun y0 : type686 a0 => (x0 y0) /\ ((forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> x1 y1) /\ ((@INTERS a0 y0) = x2)).
Definition term39 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term49 (a0 : Type') := forall y0 : type180 a0, forall y1 : type686 a0, forall y2 : a0 -> Prop, ((y0 (@INSERT (a0 -> Prop) y2 (@EMPTY (a0 -> Prop)))) /\ (y1 y2)) -> @INTERSECTION_OF a0 y0 y1 y2.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @IN (a0 -> Prop) x0 (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop))).
Definition term29 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : Prop) := ((x1 = x2) -> (x0 x1) = x3) -> ((@IN (a0 -> Prop) x1 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) -> x0 x1) = ((x1 = x2) -> x3).
Definition term4 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ (x1 x2).
Definition term47 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, ((x0 (@INSERT (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))) /\ (x1 y0)) -> @INTERSECTION_OF a0 x0 x1 y0.
Definition term14 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = (y0 = y1)) x0.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 y0.
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) = y0) -> (y0 -> (x1 x2) = y1) -> ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 x2) = (y0 -> y1)) x3.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 x2.
Definition term1 (a0 : Type') (x0 : type180 a0) := forall y0 : type686 a0, (@INTERSECTION_OF a0 x0 y0) = (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> y0 y3) /\ ((@INTERS a0 y2) = y1))).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := @INTERS a0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x0 = x1) -> True.
Definition term0 (a0 : Type') (x0 : type180 a0) := (fun y0 : type180 a0 => forall y1 : type686 a0, (@INTERSECTION_OF a0 y0 y1) = (fun y2 : a0 -> Prop => exists y3 : type686 a0, (y0 y3) /\ ((forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y3) -> y1 y4) /\ ((@INTERS a0 y3) = y2)))) x0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) = x3) -> (x3 -> (x1 x2) = x4) -> ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 x2) = (x3 -> x4).
Definition term10 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := exists y0 : type686 a0, (x0 y0) /\ ((forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> x1 y1) /\ ((@INTERS a0 y0) = x2)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : Prop) := forall y0 : Prop, ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) = x3) -> (x3 -> (x1 x2) = y0) -> ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 x2) = (x3 -> y0).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term35 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) = y0) -> (y0 -> (x1 x2) = y1) -> ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 x2) = (y0 -> y1).
Definition term21 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) = x3) -> (x3 -> (x1 x2) = y0) -> ((@IN (a0 -> Prop) x2 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 x2) = (x3 -> y0)) x4.
Definition term48 (a0 : Type') (x0 : type180 a0) := forall y0 : type686 a0, forall y1 : a0 -> Prop, ((x0 (@INSERT (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) /\ (y0 y1)) -> @INTERSECTION_OF a0 x0 y0 y1.
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term15 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0).
Definition term13 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => exists y1 : type686 a0, (x0 y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> x1 y2) /\ ((@INTERS a0 y1) = y0))) x2).
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN (a0 -> Prop) x1 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) = (x1 = x2)) -> ((x1 = x2) -> (x0 x1) = x3) -> ((@IN (a0 -> Prop) x1 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) -> x0 x1) = ((x1 = x2) -> x3).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := and (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 y0).
Definition term31 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((x1 = x2) -> (x0 x1) = True) -> ((@IN (a0 -> Prop) x1 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) -> x0 x1) = ((x1 = x2) -> True).
Definition term18 (a0 : Type') (x0 : type180 a0) (x1 : a0 -> Prop) := and (x0 (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop)))).
Definition term3 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := fun y0 : a0 -> Prop => exists y1 : type686 a0, (x0 y1) /\ ((forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y1) -> x1 y2) /\ ((@INTERS a0 y1) = y0)).
Definition term5 (a0 : Type') (x0 : type180 a0) (x1 : a0 -> Prop) := x0 (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop))).
Definition term9 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> x1 y3) /\ ((@INTERS a0 y2) = y1))) y0) x2.
Definition term2 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (fun y0 : type686 a0 => (@INTERSECTION_OF a0 x0 y0) = (fun y1 : a0 -> Prop => exists y2 : type686 a0, (x0 y2) /\ ((forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y2) -> y0 y3) /\ ((@INTERS a0 y2) = y1)))) x1.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> x1 y0.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := @eq (a0 -> Prop) (@INTERS a0 (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))).
Definition term46 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := ((x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ (x1 x2)) -> @INTERSECTION_OF a0 x0 x1 x2.
Definition term37 (a0 : Type') := forall y0 : a0 -> Prop, True.
