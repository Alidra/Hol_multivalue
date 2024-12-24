Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 := @eq Prop (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_eq y0 y1) = (treal_eq y1 y0)).
Definition term22 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_eq y0 y1) = (treal_eq y1 y0).
Definition term48 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y2) = (treal_eq y2 (@pair hreal hreal x0 x1))) (@pair hreal hreal y0 y1).
Definition term31 := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, (treal_eq y2 y3) = (treal_eq y3 y2)) (@pair hreal hreal y0 y1).
Definition term46 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y1) = (treal_eq y1 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 y0).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term9 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0))) x3.
Definition term12 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term26 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (treal_eq (@pair hreal hreal x0 x1) y0) = (treal_eq y0 (@pair hreal hreal x0 x1)).
Definition term7 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1))) x2.
Definition term55 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term21 := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_eq y1 y2) = (treal_eq y2 y1)) y0.
Definition term52 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq Prop ((hreal_add x0 x1) = (hreal_add x2 x3)).
Definition term20 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_eq x0 y0) = (treal_eq y0 x0).
Definition term54 := forall y0 : hreal, True.
Definition term29 (x0 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_eq y1 y2) = (treal_eq y2 y1)) (@pair hreal hreal x0 y0).
Definition term41 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y1) = (treal_eq y1 (@pair hreal hreal x0 x1))) y0).
Definition term23 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_eq y1 y2) = (treal_eq y2 y1)) y0).
Definition term27 (x0 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_eq y1 y2) = (treal_eq y2 y1)) (@pair hreal hreal x0 y0).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term5 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2))) x1.
Definition term36 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y0) = (treal_eq y0 (@pair hreal hreal x0 x1)).
Definition term37 (x0 : hreal) (x1 : hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y0) = (treal_eq y0 (@pair hreal hreal x0 x1))) x2.
Definition term18 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_eq y0 y1) = (treal_eq y1 y0).
Definition term50 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)) = (treal_eq (@pair hreal hreal y0 y1) (@pair hreal hreal x0 x1)).
Definition term35 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y2) = (treal_eq y2 (@pair hreal hreal x0 x1))) (@pair hreal hreal y0 y1).
Definition term33 := forall y0 : hreal, forall y1 : hreal, forall y2 : prod hreal hreal, (treal_eq (@pair hreal hreal y0 y1) y2) = (treal_eq y2 (@pair hreal hreal y0 y1)).
Definition term30 (x0 : hreal) := forall y0 : hreal, forall y1 : prod hreal hreal, (treal_eq (@pair hreal hreal x0 y0) y1) = (treal_eq y1 (@pair hreal hreal x0 y0)).
Definition term17 := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, (treal_eq y2 y3) = (treal_eq y3 y2)) (@pair hreal hreal y0 y1).
Definition term15 (x0 : type1233) := forall y0 : hreal, forall y1 : hreal, x0 (@pair hreal hreal y0 y1).
Definition term6 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1)).
Definition term4 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2)).
Definition term42 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (treal_eq (@pair hreal hreal x0 x1) y0) = (treal_eq y0 (@pair hreal hreal x0 x1))).
Definition term38 (x0 : hreal) (x1 : hreal) (x2 : prod hreal hreal) := treal_eq (@pair hreal hreal x0 x1) x2.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term32 := fun y0 : hreal => forall y1 : hreal, forall y2 : prod hreal hreal, (treal_eq (@pair hreal hreal y0 y1) y2) = (treal_eq y2 (@pair hreal hreal y0 y1)).
Definition term14 (x0 : type1233) := forall y0 : prod hreal hreal, x0 y0.
Definition term56 (x0 : Prop) := forall y0 : hreal, x0.
Definition term49 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)) = (treal_eq (@pair hreal hreal y0 y1) (@pair hreal hreal x0 x1)).
Definition term19 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_eq y0 y1) = (treal_eq y1 y0)) x0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term34 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y1) = (treal_eq y1 (@pair hreal hreal x0 x1))) y0.
Definition term25 (x0 : hreal) (x1 : hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_eq y0 y1) = (treal_eq y1 y0)) (@pair hreal hreal x0 x1).
Definition term39 (x0 : prod hreal hreal) (x1 : hreal) (x2 : hreal) := treal_eq x0 (@pair hreal hreal x1 x2).
Definition term16 := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_eq y1 y2) = (treal_eq y2 y1)) y0.
Definition term47 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x1 x2) (@pair hreal hreal x0 y0)) = (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x1 x2)).
Definition term8 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0)).
Definition term45 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (treal_eq (@pair hreal hreal x1 x2) (@pair hreal hreal x0 y0)) = (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x1 x2)).
Definition term53 := fun y0 : hreal => True.
Definition term51 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq Prop (treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)).
Definition term28 (x0 : hreal) := fun y0 : hreal => forall y1 : prod hreal hreal, (treal_eq (@pair hreal hreal x0 y0) y1) = (treal_eq y1 (@pair hreal hreal x0 y0)).
Definition term44 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y1) = (treal_eq y1 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 y0).
Definition term10 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term40 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y1) = (treal_eq y1 (@pair hreal hreal x0 x1))) y0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term3 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_eq (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = ((hreal_add y0 y1) = (hreal_add y2 y3))) x0.
Definition term43 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : prod hreal hreal => (treal_eq (@pair hreal hreal x0 x1) y0) = (treal_eq y0 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 x3).
