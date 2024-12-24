Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := (forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> x1 y1) -> x1 y0) -> forall y0 : a0, x1 y0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> a1) := fun y0 : a0 => (x0 y0 x1) -> (x2 y0) = (x3 y0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : type549 a0 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0, (forall y3 : a0, (x0 y3 y2) -> (y0 y3) = (y1 y3)) -> (x1 y0 y2) = (x1 y1 y2).
Definition term15 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> x1 y1) -> x1 y0.
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> a1) := forall y0 : a0, (x0 y0 x1) -> (x2 y0) = (x3 y0).
Definition term38 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) := imp (forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> (x1 y1) = (x2 y1)) -> (x1 y0) = (x2 y0)).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> a1) := imp (forall y0 : a0, (x0 y0 x1) -> (x2 y0) = (x3 y0)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, x0 y0.
Definition term50 (a0 : Type') (a1 : Type') (x0 : type549 a0 a1) (x1 : a0 -> a1) (x2 : a0) := @eq a1 (x0 x1 x2).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (fun y1 : a0 => (x0 y1) = (x1 y1)) y0.
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> a1) := fun y0 : a0 => (x0 y0 x1) -> (fun y1 : a0 => (x2 y1) = (x3 y1)) y0.
Definition term57 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : type549 a0 a1) := (forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0, (forall y3 : a0, (x0 y3 y2) -> (y0 y3) = (y1 y3)) -> (x1 y0 y2) = (x1 y1 y2)) -> forall y0 : a0 -> a1, forall y1 : a0 -> a1, ((forall y2 : a0, (y0 y2) = (x1 y0 y2)) /\ (forall y2 : a0, (y1 y2) = (x1 y1 y2))) -> y0 = y1.
Definition term45 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : type549 a0 a1) (x3 : a0 -> a1) := forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> (x1 y1) = (x3 y1)) -> (x2 x1 y0) = (x2 x3 y0).
Definition term51 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type549 a0 a1) (x2 : a0 -> a1) (x3 : a0) := imp ((x1 x0 x3) = (x1 x2 x3)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type549 a0 a1) (x2 : a0 -> a1) := (forall y0 : a0, (x0 y0) = (x1 x0 y0)) /\ (forall y0 : a0, (x2 y0) = (x1 x2 y0)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) := forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> (x1 y1) = (x2 y1)) -> (x1 y0) = (x2 y0).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @eq a1 (x0 x1).
Definition term54 (a0 : Type') (a1 : Type') (x0 : type549 a0 a1) (x1 : a0 -> a1) (x2 : a0 -> a1) := ((forall y0 : a0, (x1 y0) = (x0 x1 y0)) /\ (forall y0 : a0, (x2 y0) = (x0 x2 y0))) -> x1 = x2.
Definition term17 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := (forall y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1) -> forall y0 : a0, x1 y0.
Definition term33 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) := fun y0 : a0 => (forall y1 : a0, (x0 y1 y0) -> (fun y2 : a0 => (x1 y2) = (x2 y2)) y1) -> (fun y1 : a0 => (x1 y1) = (x2 y1)) y0.
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (x0 y0) = (x1 y0)) x2.
Definition term32 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) (x3 : a0) := (forall y0 : a0, (x0 y0 x3) -> (x1 y0) = (x2 y0)) -> (x1 x3) = (x2 x3).
Definition term47 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : type549 a0 a1) (x3 : a0 -> a1) (x4 : a0) := (forall y0 : a0, (x0 y0 x4) -> (x1 y0) = (x3 y0)) -> (x2 x1 x4) = (x2 x3 x4).
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) := (forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> (fun y2 : a0 => (x1 y2) = (x2 y2)) y1) -> (fun y1 : a0 => (x1 y1) = (x2 y1)) y0) -> forall y0 : a0, (fun y1 : a0 => (x1 y1) = (x2 y1)) y0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1402 a0) := (@WF a0 x0) -> forall y0 : type549 a0 a1, (forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0, (forall y4 : a0, (x0 y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, ((forall y3 : a0, (y1 y3) = (y0 y1 y3)) /\ (forall y3 : a0, (y2 y3) = (y0 y2 y3))) -> y1 = y2.
Definition term48 (a0 : Type') (a1 : Type') (x0 : type549 a0 a1) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (x1 y0) = (x0 x1 y0)) x2.
Definition term4 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1.
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type549 a0 a1) (x2 : a0 -> a1) (x3 : a0) := ((x1 x0 x3) = (x1 x2 x3)) -> (x1 x0 x3) = (x1 x2 x3).
Definition term37 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) := imp (forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> (fun y2 : a0 => (x1 y2) = (x2 y2)) y1) -> (fun y1 : a0 => (x1 y1) = (x2 y1)) y0).
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> a1) := imp (forall y0 : a0, (x0 y0 x1) -> (fun y1 : a0 => (x2 y1) = (x3 y1)) y0).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) := forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> (fun y2 : a0 => (x1 y2) = (x2 y2)) y1) -> (fun y1 : a0 => (x1 y1) = (x2 y1)) y0.
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> a1) (x4 : a0) := (x0 x4 x1) -> (fun y0 : a0 => (x2 y0) = (x3 y0)) x4.
Definition term12 (a0 : Type') (a1 : Type') (x0 : type549 a0 a1) (x1 : a0 -> a1) := forall y0 : a0, (x1 y0) = (x0 x1 y0).
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : type549 a0 a1) (x3 : a0 -> a1) (x4 : a0) := (fun y0 : a0 => (forall y1 : a0, (x0 y1 y0) -> (x1 y1) = (x3 y1)) -> (x2 x1 y0) = (x2 x3 y0)) x4.
Definition term5 (a0 : Type') (x0 : type1402 a0) := imp (@WF a0 x0).
Definition term44 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : type549 a0 a1) (x3 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> (x1 y2) = (y0 y2)) -> (x2 x1 y1) = (x2 y0 y1)) x3.
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) := fun y0 : a0 => (forall y1 : a0, (x0 y1 y0) -> (x1 y1) = (x2 y1)) -> (x1 y0) = (x2 y0).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> a1) := forall y0 : a0, (x0 y0 x1) -> (fun y1 : a0 => (x2 y1) = (x3 y1)) y0.
Definition term56 (a0 : Type') (a1 : Type') (x0 : type549 a0 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> a1, ((forall y2 : a0, (y0 y2) = (x0 y0 y2)) /\ (forall y2 : a0, (y1 y2) = (x0 y1 y2))) -> y0 = y1.
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) := (forall y0 : a0, (forall y1 : a0, (x0 y1 y0) -> (x1 y1) = (x2 y1)) -> (x1 y0) = (x2 y0)) -> forall y0 : a0, (x1 y0) = (x2 y0).
Definition term6 (a0 : Type') (x0 : type1402 a0) := imp (forall y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := fun y0 : a0 => (fun y1 : a0 => (x0 y1) = (x1 y1)) y0.
Definition term52 (a0 : Type') (a1 : Type') (x0 : type549 a0 a1) (x1 : a0 -> a1) (x2 : a0 -> a1) (x3 : a0) := ((x0 x1 x3) = (x0 x2 x3)) -> (x1 x3) = (x2 x3).
Definition term13 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1) x1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : a0 -> a1) (x3 : a0) := (forall y0 : a0, (x0 y0 x3) -> (fun y1 : a0 => (x1 y1) = (x2 y1)) y0) -> (fun y0 : a0 => (x1 y0) = (x2 y0)) x3.
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : type549 a0 a1) (x2 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, forall y2 : a0, (forall y3 : a0, (x0 y3 y2) -> (y0 y3) = (y1 y3)) -> (x1 y0 y2) = (x1 y1 y2)) x2.
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1402 a0) := forall y0 : type549 a0 a1, (forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0, (forall y4 : a0, (x0 y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, ((forall y3 : a0, (y1 y3) = (y0 y1 y3)) /\ (forall y3 : a0, (y2 y3) = (y0 y2 y3))) -> y1 = y2.
Definition term22 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := imp (x0 x1 x2).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term18 (a0 : Type') (x0 : type1402 a0) := (forall y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1) -> forall y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1402 a0) := (forall y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1) -> forall y0 : type549 a0 a1, (forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0, (forall y4 : a0, (x0 y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, ((forall y3 : a0, (y1 y3) = (y0 y1 y3)) /\ (forall y3 : a0, (y2 y3) = (y0 y2 y3))) -> y1 = y2.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0 -> a1) (x3 : a0 -> a1) (x4 : a0) := (x0 x4 x1) -> (x2 x4) = (x3 x4).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1402 a0) (x1 : a0 -> a1) (x2 : type549 a0 a1) := forall y0 : a0 -> a1, forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> (x1 y2) = (y0 y2)) -> (x2 x1 y1) = (x2 y0 y1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term55 (a0 : Type') (a1 : Type') (x0 : type549 a0 a1) (x1 : a0 -> a1) := forall y0 : a0 -> a1, ((forall y1 : a0, (x1 y1) = (x0 x1 y1)) /\ (forall y1 : a0, (y0 y1) = (x0 y0 y1))) -> x1 = y0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := fun y0 : a0 => (x0 y0) = (x1 y0).
