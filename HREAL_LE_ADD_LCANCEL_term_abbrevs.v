Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0).
Definition term18 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => ((hreal_add x0 x1) = (hreal_add x0 y0)) = (x1 = y0)) x2.
Definition term39 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_le (hreal_add x0 y0) (hreal_add x0 y1)) = (hreal_le y0 y1).
Definition term6 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1).
Definition term37 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term32 (x0 : hreal) (x1 : hreal) := @eq Prop (exists y0 : hreal, x0 = (hreal_add x1 y0)).
Definition term33 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_le (hreal_add x0 x1) (hreal_add x0 y0)) = (hreal_le x1 y0).
Definition term1 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_add x0 x1) x2.
Definition term36 := forall y0 : hreal, True.
Definition term21 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0))) x2.
Definition term26 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_le (hreal_add x1 x0) (hreal_add x1 x2).
Definition term42 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_le (hreal_add y0 y1) (hreal_add y0 y2)) = (hreal_le y1 y2).
Definition term40 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_le (hreal_add x0 y0) (hreal_add x0 y1)) = (hreal_le y0 y1).
Definition term15 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, ((hreal_add x0 y0) = (hreal_add x0 y1)) = (y0 = y1).
Definition term13 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2)).
Definition term12 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2).
Definition term9 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1)).
Definition term8 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1).
Definition term27 (x0 : hreal) (x1 : hreal) (x2 : hreal) := exists y0 : hreal, (hreal_add x1 x0) = (hreal_add (hreal_add x1 x2) y0).
Definition term4 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0).
Definition term41 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_le (hreal_add y0 y1) (hreal_add y0 y2)) = (hreal_le y1 y2).
Definition term11 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2)).
Definition term10 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2).
Definition term38 (x0 : Prop) := forall y0 : hreal, x0.
Definition term7 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1)).
Definition term35 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_le (hreal_add x0 x1) (hreal_add x0 y0)) = (hreal_le x1 y0).
Definition term17 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, ((hreal_add x0 x1) = (hreal_add x0 y0)) = (x1 = y0).
Definition term3 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0)).
Definition term24 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_le x0 y0) = (exists y1 : hreal, y0 = (hreal_add x0 y1))) x1.
Definition term31 (x0 : hreal) (x1 : hreal) (x2 : hreal) := @eq Prop (hreal_le (hreal_add x1 x0) (hreal_add x1 x2)).
Definition term25 (x0 : hreal) (x1 : hreal) := exists y0 : hreal, x0 = (hreal_add x1 y0).
Definition term22 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) = (exists y2 : hreal, y1 = (hreal_add y0 y2))) x0.
Definition term23 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) = (exists y1 : hreal, y0 = (hreal_add x0 y1)).
Definition term20 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1))) x1.
Definition term16 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, ((hreal_add x0 y0) = (hreal_add x0 y1)) = (y0 = y1)) x1.
Definition term28 (x0 : hreal) (x1 : hreal) := @eq hreal (hreal_add x0 x1).
Definition term5 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0)).
Definition term34 := fun y0 : hreal => True.
Definition term0 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add x0 (hreal_add x1 x2).
Definition term29 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (hreal_add x1 x0) = (hreal_add (hreal_add x1 x2) y0).
Definition term19 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2))) x0.
Definition term14 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y1) = (hreal_add y0 y2)) = (y1 = y2)) x0.
Definition term30 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => x0 = (hreal_add x1 y0).
