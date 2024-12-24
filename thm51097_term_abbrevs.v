Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : type1412 a0 a1 a2) (x2 : a0) := forall y0 : a1, (x0 (@pair a0 a1 x2 y0)) = (x1 x2 y0).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := fun y0 : a0 => fun y1 : a1 => x0 y0 y1.
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) := fun y0 : a1 => x0 x1 y0.
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) (x2 : a1) := @eq a2 (x0 (@pair a0 a1 x1 x2)).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := exists y0 : type1209 a0 a1 a2, forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = ((fun y3 : a0 => fun y4 : a1 => x0 y3 y4) y1 y2).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := exists y0 : type1209 a0 a1 a2, forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = (x0 y1 y2).
Definition term10 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : a0) (x2 : a1) := x0 (@pair a0 a1 x1 x2).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := (fun y0 : a0 => fun y1 : a1 => x0 y0 y1) x1 x2.
Definition term11 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : type1412 a0 a1 a2) (x2 : a0) := fun y0 : a1 => (x0 (@pair a0 a1 x2 y0)) = ((fun y1 : a0 => fun y2 : a1 => x1 y1 y2) x2 y0).
Definition term8 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := (fun y0 : a1 => x0 x1 y0) x2.
Definition term12 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : type1412 a0 a1 a2) (x2 : a0) := fun y0 : a1 => (x0 (@pair a0 a1 x2 y0)) = (x1 x2 y0).
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : type1412 a0 a1 a2) := forall y0 : a0, forall y1 : a1, (x0 (@pair a0 a1 y0 y1)) = (x1 y0 y1).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : type1412 a0 a1 a2) := forall y0 : a0, forall y1 : a1, (x0 (@pair a0 a1 y0 y1)) = ((fun y2 : a0 => fun y3 : a1 => x1 y2 y3) y0 y1).
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : type1412 a0 a1 a2) := fun y0 : a0 => forall y1 : a1, (x0 (@pair a0 a1 y0 y1)) = ((fun y2 : a0 => fun y3 : a1 => x1 y2 y3) y0 y1).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := (fun y0 : type1412 a0 a1 a2 => exists y1 : type1209 a0 a1 a2, forall y2 : a0, forall y3 : a1, (y1 (@pair a0 a1 y2 y3)) = (y0 y2 y3)) x0.
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) := (fun y0 : a0 => fun y1 : a1 => x0 y0 y1) x1.
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : type1412 a0 a1 a2) (x2 : a0) := forall y0 : a1, (x0 (@pair a0 a1 x2 y0)) = ((fun y1 : a0 => fun y2 : a1 => x1 y1 y2) x2 y0).
Definition term19 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := fun y0 : type1209 a0 a1 a2 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = ((fun y3 : a0 => fun y4 : a1 => x0 y3 y4) y1 y2).
Definition term18 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := fun y0 : type1209 a0 a1 a2 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = (x0 y1 y2).
Definition term16 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : type1412 a0 a1 a2) := fun y0 : a0 => forall y1 : a1, (x0 (@pair a0 a1 y0 y1)) = (x1 y0 y1).
