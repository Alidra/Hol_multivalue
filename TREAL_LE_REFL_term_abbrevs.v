Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => treal_le y2 y2) (@pair hreal hreal y0 y1).
Definition term20 := forall y0 : prod hreal hreal, treal_le y0 y0.
Definition term30 := fun y0 : hreal => forall y1 : hreal, treal_le (@pair hreal hreal y0 y1) (@pair hreal hreal y0 y1).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term7 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0))) x3.
Definition term5 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1))) x2.
Definition term35 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => treal_le y0 y0) x0.
Definition term27 (x0 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => treal_le y1 y1) (@pair hreal hreal x0 y0).
Definition term34 := forall y0 : hreal, True.
Definition term9 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add x0 x1) (hreal_add x2 x3).
Definition term21 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => treal_le y1 y1) y0).
Definition term3 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2))) x1.
Definition term15 := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => treal_le y1 y1) y0.
Definition term17 := fun y0 : prod hreal hreal => treal_le y0 y0.
Definition term24 (x0 : hreal) (x1 : hreal) := treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal x0 x1).
Definition term31 := forall y0 : hreal, forall y1 : hreal, treal_le (@pair hreal hreal y0 y1) (@pair hreal hreal y0 y1).
Definition term16 := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => treal_le y2 y2) (@pair hreal hreal y0 y1).
Definition term14 (x0 : type1233) := forall y0 : hreal, forall y1 : hreal, x0 (@pair hreal hreal y0 y1).
Definition term4 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1)).
Definition term2 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2)).
Definition term0 (x0 : hreal) := (fun y0 : hreal => hreal_le y0 y0) x0.
Definition term13 (x0 : type1233) := forall y0 : prod hreal hreal, x0 y0.
Definition term36 (x0 : Prop) := forall y0 : hreal, x0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term23 (x0 : hreal) (x1 : hreal) := (fun y0 : prod hreal hreal => treal_le y0 y0) (@pair hreal hreal x0 x1).
Definition term32 (x0 : hreal) (x1 : hreal) := hreal_le (hreal_add x0 x1) (hreal_add x0 x1).
Definition term8 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term19 := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => treal_le y1 y1) y0.
Definition term6 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0)).
Definition term33 := fun y0 : hreal => True.
Definition term22 := @eq Prop (forall y0 : prod hreal hreal, treal_le y0 y0).
Definition term28 (x0 : hreal) := forall y0 : hreal, treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x0 y0).
Definition term25 (x0 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => treal_le y1 y1) (@pair hreal hreal x0 y0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term26 (x0 : hreal) := fun y0 : hreal => treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x0 y0).
Definition term1 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_le (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = (hreal_le (hreal_add y0 y1) (hreal_add y2 y3))) x0.
