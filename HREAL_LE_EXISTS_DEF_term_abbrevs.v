Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_le x0 y0) -> exists y1 : hreal, y0 = (hreal_add x0 y1)) x1.
Definition term9 (x0 : hreal) := fun y0 : hreal => hreal_le x0 y0.
Definition term1 (x0 : hreal) := forall y0 : hreal, hreal_le x0 (hreal_add x0 y0).
Definition term16 (x0 : hreal) (x1 : hreal) := ((hreal_le x0 x1) -> exists y0 : hreal, x1 = (hreal_add x0 y0)) /\ ((exists y0 : hreal, x1 = (hreal_add x0 y0)) -> hreal_le x0 x1).
Definition term3 (x0 : hreal) (x1 : hreal) := hreal_le x0 (hreal_add x0 x1).
Definition term18 := forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (exists y2 : hreal, y1 = (hreal_add y0 y2)).
Definition term15 (x0 : hreal) (x1 : hreal) := (exists y0 : hreal, x1 = (hreal_add x0 y0)) -> hreal_le x0 x1.
Definition term11 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => hreal_le x0 y0) (hreal_add x0 x1).
Definition term8 (x0 : hreal) (x1 : hreal) := exists y0 : hreal, x0 = (hreal_add x1 y0).
Definition term4 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) -> exists y2 : hreal, y1 = (hreal_add y0 y2)) x0.
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, hreal_le y0 (hreal_add y0 y1)) x0.
Definition term17 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) = (exists y1 : hreal, y0 = (hreal_add x0 y1)).
Definition term12 (x0 : hreal) (x1 : hreal) := @eq Prop ((fun y0 : hreal => hreal_le x0 y0) x1).
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => hreal_le x0 (hreal_add x0 y0)) x1.
Definition term13 (x0 : hreal) (x1 : hreal) := @eq Prop (hreal_le x0 x1).
Definition term7 (x0 : hreal) (x1 : hreal) := (hreal_le x1 x0) -> exists y0 : hreal, x0 = (hreal_add x1 y0).
Definition term10 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => hreal_le x0 y0) x1.
Definition term5 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) -> exists y1 : hreal, y0 = (hreal_add x0 y1).
Definition term14 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => x0 = (hreal_add x1 y0).
