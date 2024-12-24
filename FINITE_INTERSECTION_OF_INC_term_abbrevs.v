Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (a0 : Type') := fun y0 : type686 a0 => forall y1 : a0 -> Prop, (y0 y1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0 y1.
Definition term20 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ((@FINITE (a0 -> Prop) (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop)))) /\ (x0 x1)) -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = True.
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term19 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := ((x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ (x1 x2)) -> (@INTERSECTION_OF a0 x0 x1 x2) = True.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := @FINITE (a0 -> Prop) (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term33 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term30 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (x0 y0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y0.
Definition term4 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := (fun y0 : type686 a0 => forall y1 : a0 -> Prop, ((x0 (@INSERT (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) /\ (y0 y1)) -> @INTERSECTION_OF a0 x0 y0 y1) x1.
Definition term24 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (x0 x1) -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = True.
Definition term8 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ (x1 x2).
Definition term5 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, ((x0 (@INSERT (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))) /\ (x1 y0)) -> @INTERSECTION_OF a0 x0 x1 y0.
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term18 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) := ((x0 x1) -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = x2) -> ((x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = ((x0 x1) -> x2).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE (a0 -> Prop) (@INSERT (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))).
Definition term37 (a0 : Type') := forall y0 : type686 a0, True.
Definition term15 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((x0 x1) = x2) -> (x2 -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = y0) -> ((x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = (x2 -> y0)) x3.
Definition term6 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((x0 (@INSERT (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))) /\ (x1 y0)) -> @INTERSECTION_OF a0 x0 x1 y0) x2.
Definition term35 (a0 : Type') := fun y0 : type686 a0 => True.
Definition term23 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (@FINITE (a0 -> Prop) (@INSERT (a0 -> Prop) x1 (@EMPTY (a0 -> Prop)))) /\ (x0 x1).
Definition term14 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) := forall y0 : Prop, ((x0 x1) = x2) -> (x2 -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = y0) -> ((x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = (x2 -> y0).
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term29 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term17 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) := ((x0 x1) = (x0 x1)) -> ((x0 x1) -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = x2) -> ((x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = ((x0 x1) -> x2).
Definition term12 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((x0 x1) = y0) -> (y0 -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = y1) -> ((x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = (y0 -> y1).
Definition term11 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term36 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0 -> Prop, (y0 y1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) y0 y1.
Definition term3 (a0 : Type') (x0 : type180 a0) := forall y0 : type686 a0, forall y1 : a0 -> Prop, ((x0 (@INSERT (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) /\ (y0 y1)) -> @INTERSECTION_OF a0 x0 y0 y1.
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @FINITE a0 (@INSERT a0 y0 (@EMPTY a0))) x0.
Definition term25 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ((x0 x1) -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = True) -> ((x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = ((x0 x1) -> True).
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : type686 a0, x0.
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1.
Definition term16 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : Prop) := ((x0 x1) = x2) -> (x2 -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = x3) -> ((x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = (x2 -> x3).
Definition term28 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (x0 y0) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 y0.
Definition term13 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 x1) = y0) -> (y0 -> (@INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = y1) -> ((x0 x1) -> @INTERSECTION_OF a0 (@FINITE (a0 -> Prop)) x0 x1) = (y0 -> y1)) x2.
Definition term1 (a0 : Type') (x0 : a0) := @FINITE a0 (@INSERT a0 x0 (@EMPTY a0)).
Definition term27 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (x0 x1) -> True.
Definition term7 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := ((x0 (@INSERT (a0 -> Prop) x2 (@EMPTY (a0 -> Prop)))) /\ (x1 x2)) -> @INTERSECTION_OF a0 x0 x1 x2.
Definition term31 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term2 (a0 : Type') (x0 : type180 a0) := (fun y0 : type180 a0 => forall y1 : type686 a0, forall y2 : a0 -> Prop, ((y0 (@INSERT (a0 -> Prop) y2 (@EMPTY (a0 -> Prop)))) /\ (y1 y2)) -> @INTERSECTION_OF a0 y0 y1 y2) x0.
