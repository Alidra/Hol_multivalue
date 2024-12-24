Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (x0 : type1160 a0) (x1 : Prop) := ((forall y0 : option a0, x0 y0) -> ((x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = x1) -> ((forall y0 : option a0, x0 y0) -> (x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = ((forall y0 : option a0, x0 y0) -> x1).
Definition term22 (a0 : Type') (x0 : type1160 a0) := (forall y0 : option a0, x0 y0) -> ((x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = True.
Definition term21 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term20 (a0 : Type') := forall y0 : a0, True.
Definition term12 (a0 : Type') (x0 : type1160 a0) (x1 : Prop) := ((forall y0 : option a0, x0 y0) = (forall y0 : option a0, x0 y0)) -> ((forall y0 : option a0, x0 y0) -> ((x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = x1) -> ((forall y0 : option a0, x0 y0) -> (x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = ((forall y0 : option a0, x0 y0) -> x1).
Definition term14 (a0 : Type') (x0 : type1160 a0) (x1 : option a0) := (fun y0 : option a0 => x0 y0) x1.
Definition term10 (a0 : Type') (x0 : type1160 a0) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((forall y1 : option a0, x0 y1) = x1) -> (x1 -> ((x0 (@None a0)) /\ (forall y1 : a0, x0 (@Some a0 y1))) = y0) -> ((forall y1 : option a0, x0 y1) -> (x0 (@None a0)) /\ (forall y1 : a0, x0 (@Some a0 y1))) = (x1 -> y0)) x2.
Definition term2 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term19 (a0 : Type') (x0 : type1160 a0) := forall y0 : a0, x0 (@Some a0 y0).
Definition term18 (a0 : Type') := fun y0 : a0 => True.
Definition term15 (a0 : Type') (x0 : type1160 a0) := and (x0 (@None a0)).
Definition term9 (a0 : Type') (x0 : type1160 a0) (x1 : Prop) := forall y0 : Prop, ((forall y1 : option a0, x0 y1) = x1) -> (x1 -> ((x0 (@None a0)) /\ (forall y1 : a0, x0 (@Some a0 y1))) = y0) -> ((forall y1 : option a0, x0 y1) -> (x0 (@None a0)) /\ (forall y1 : a0, x0 (@Some a0 y1))) = (x1 -> y0).
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term5 (a0 : Type') (x0 : type1160 a0) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : option a0, x0 y2) = y0) -> (y0 -> ((x0 (@None a0)) /\ (forall y2 : a0, x0 (@Some a0 y2))) = y1) -> ((forall y2 : option a0, x0 y2) -> (x0 (@None a0)) /\ (forall y2 : a0, x0 (@Some a0 y2))) = (y0 -> y1).
Definition term4 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term11 (a0 : Type') (x0 : type1160 a0) (x1 : Prop) (x2 : Prop) := ((forall y0 : option a0, x0 y0) = x1) -> (x1 -> ((x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = x2) -> ((forall y0 : option a0, x0 y0) -> (x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = (x1 -> x2).
Definition term17 (a0 : Type') (x0 : type1160 a0) := fun y0 : a0 => x0 (@Some a0 y0).
Definition term0 (a0 : Type') (x0 : type1160 a0) := (fun y0 : type1160 a0 => ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1) x0.
Definition term26 (a0 : Type') (x0 : type1160 a0) := ((forall y0 : option a0, x0 y0) -> (x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) /\ (((x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) -> forall y0 : option a0, x0 y0).
Definition term8 (a0 : Type') (x0 : type1160 a0) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : option a0, x0 y2) = y0) -> (y0 -> ((x0 (@None a0)) /\ (forall y2 : a0, x0 (@Some a0 y2))) = y1) -> ((forall y2 : option a0, x0 y2) -> (x0 (@None a0)) /\ (forall y2 : a0, x0 (@Some a0 y2))) = (y0 -> y1)) x1.
Definition term23 (a0 : Type') (x0 : type1160 a0) := ((forall y0 : option a0, x0 y0) -> ((x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = True) -> ((forall y0 : option a0, x0 y0) -> (x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) = ((forall y0 : option a0, x0 y0) -> True).
Definition term6 (a0 : Type') (x0 : type1160 a0) := forall y0 : option a0, x0 y0.
Definition term25 (a0 : Type') (x0 : type1160 a0) := (forall y0 : option a0, x0 y0) -> True.
Definition term16 (a0 : Type') (x0 : type1160 a0) (x1 : a0) := x0 (@Some a0 x1).
Definition term24 (a0 : Type') (x0 : type1160 a0) := (forall y0 : option a0, x0 y0) -> (x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0)).
Definition term7 (a0 : Type') (x0 : type1160 a0) := (x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0)).
Definition term27 (a0 : Type') := forall y0 : type1160 a0, (forall y1 : option a0, y0 y1) = ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))).
Definition term1 (a0 : Type') (x0 : type1160 a0) := ((x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) -> forall y0 : option a0, x0 y0.
