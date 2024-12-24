Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => treal_eq y2 y2) (@pair hreal hreal y0 y1).
Definition term28 := fun y0 : hreal => forall y1 : hreal, treal_eq (@pair hreal hreal y0 y1) (@pair hreal hreal y0 y1).
Definition term6 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0))) x3.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term4 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1))) x2.
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term24 (x0 : hreal) := fun y0 : hreal => treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x0 y0).
Definition term25 (x0 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => treal_eq y1 y1) (@pair hreal hreal x0 y0).
Definition term31 := forall y0 : hreal, True.
Definition term19 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => treal_eq y1 y1) y0).
Definition term21 (x0 : hreal) (x1 : hreal) := (fun y0 : prod hreal hreal => treal_eq y0 y0) (@pair hreal hreal x0 x1).
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2))) x1.
Definition term13 := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => treal_eq y1 y1) y0.
Definition term18 := forall y0 : prod hreal hreal, treal_eq y0 y0.
Definition term29 := forall y0 : hreal, forall y1 : hreal, treal_eq (@pair hreal hreal y0 y1) (@pair hreal hreal y0 y1).
Definition term14 := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => treal_eq y2 y2) (@pair hreal hreal y0 y1).
Definition term12 (x0 : type1233) := forall y0 : hreal, forall y1 : hreal, x0 (@pair hreal hreal y0 y1).
Definition term3 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1)).
Definition term1 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2)).
Definition term16 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => treal_eq y0 y0) x0.
Definition term11 (x0 : type1233) := forall y0 : prod hreal hreal, x0 y0.
Definition term33 (x0 : Prop) := forall y0 : hreal, x0.
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term15 := fun y0 : prod hreal hreal => treal_eq y0 y0.
Definition term17 := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => treal_eq y1 y1) y0.
Definition term5 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0)).
Definition term30 := fun y0 : hreal => True.
Definition term20 := @eq Prop (forall y0 : prod hreal hreal, treal_eq y0 y0).
Definition term22 (x0 : hreal) (x1 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x0 x1).
Definition term26 (x0 : hreal) := forall y0 : hreal, treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x0 y0).
Definition term7 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term23 (x0 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => treal_eq y1 y1) (@pair hreal hreal x0 y0).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_eq (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = ((hreal_add y0 y1) = (hreal_add y2 y3))) x0.
