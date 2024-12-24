Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 := @eq Prop (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_le y0 y1) \/ (treal_le y1 y0)).
Definition term24 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_le y0 y1) \/ (treal_le y1 y0).
Definition term50 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y2) \/ (treal_le y2 (@pair hreal hreal x0 x1))) (@pair hreal hreal y0 y1).
Definition term33 := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, (treal_le y2 y3) \/ (treal_le y3 y2)) (@pair hreal hreal y0 y1).
Definition term48 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y1) \/ (treal_le y1 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 y0).
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term10 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0))) x3.
Definition term8 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1))) x2.
Definition term58 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_le x0 y0) \/ (hreal_le y0 x0)) x1.
Definition term23 := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_le y1 y2) \/ (treal_le y2 y1)) y0.
Definition term45 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (treal_le (@pair hreal hreal x2 x3) (@pair hreal hreal x0 x1)) \/ (treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)).
Definition term57 := forall y0 : hreal, True.
Definition term12 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add x0 x1) (hreal_add x2 x3).
Definition term31 (x0 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_le y1 y2) \/ (treal_le y2 y1)) (@pair hreal hreal x0 y0).
Definition term42 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y1) \/ (treal_le y1 (@pair hreal hreal x0 x1))) y0).
Definition term25 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_le y1 y2) \/ (treal_le y2 y1)) y0).
Definition term29 (x0 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_le y1 y2) \/ (treal_le y2 y1)) (@pair hreal hreal x0 y0).
Definition term28 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (treal_le (@pair hreal hreal x0 x1) y0) \/ (treal_le y0 (@pair hreal hreal x0 x1)).
Definition term39 (x0 : hreal) (x1 : hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y0) \/ (treal_le y0 (@pair hreal hreal x0 x1))) x2.
Definition term6 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2))) x1.
Definition term55 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (hreal_le (hreal_add x2 x3) (hreal_add x0 x1)) \/ (hreal_le (hreal_add x0 x1) (hreal_add x2 x3)).
Definition term20 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_le y0 y1) \/ (treal_le y1 y0).
Definition term22 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_le x0 y0) \/ (treal_le y0 x0).
Definition term52 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)) \/ (treal_le (@pair hreal hreal y0 y1) (@pair hreal hreal x0 x1)).
Definition term37 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y2) \/ (treal_le y2 (@pair hreal hreal x0 x1))) (@pair hreal hreal y0 y1).
Definition term35 := forall y0 : hreal, forall y1 : hreal, forall y2 : prod hreal hreal, (treal_le (@pair hreal hreal y0 y1) y2) \/ (treal_le y2 (@pair hreal hreal y0 y1)).
Definition term32 (x0 : hreal) := forall y0 : hreal, forall y1 : prod hreal hreal, (treal_le (@pair hreal hreal x0 y0) y1) \/ (treal_le y1 (@pair hreal hreal x0 y0)).
Definition term19 := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, (treal_le y2 y3) \/ (treal_le y3 y2)) (@pair hreal hreal y0 y1).
Definition term17 (x0 : type1233) := forall y0 : hreal, forall y1 : hreal, x0 (@pair hreal hreal y0 y1).
Definition term7 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1)).
Definition term5 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2)).
Definition term53 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := or (treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)).
Definition term43 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (treal_le (@pair hreal hreal x0 x1) y0) \/ (treal_le y0 (@pair hreal hreal x0 x1))).
Definition term3 (x0 : hreal) (x1 : hreal) := (hreal_le x1 x0) \/ (hreal_le x0 x1).
Definition term34 := fun y0 : hreal => forall y1 : hreal, forall y2 : prod hreal hreal, (treal_le (@pair hreal hreal y0 y1) y2) \/ (treal_le y2 (@pair hreal hreal y0 y1)).
Definition term16 (x0 : type1233) := forall y0 : prod hreal hreal, x0 y0.
Definition term59 (x0 : Prop) := forall y0 : hreal, x0.
Definition term51 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, (treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)) \/ (treal_le (@pair hreal hreal y0 y1) (@pair hreal hreal x0 x1)).
Definition term38 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y0) \/ (treal_le y0 (@pair hreal hreal x0 x1)).
Definition term21 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_le y0 y1) \/ (treal_le y1 y0)) x0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term40 (x0 : prod hreal hreal) (x1 : hreal) (x2 : hreal) := (treal_le (@pair hreal hreal x1 x2) x0) \/ (treal_le x0 (@pair hreal hreal x1 x2)).
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) \/ (hreal_le y1 y0)) x0.
Definition term36 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y1) \/ (treal_le y1 (@pair hreal hreal x0 x1))) y0.
Definition term1 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) \/ (hreal_le y0 x0).
Definition term54 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := or (hreal_le (hreal_add x0 x1) (hreal_add x2 x3)).
Definition term47 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (treal_le (@pair hreal hreal x1 x2) (@pair hreal hreal x0 y0)) \/ (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x1 x2)).
Definition term27 (x0 : hreal) (x1 : hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_le y0 y1) \/ (treal_le y1 y0)) (@pair hreal hreal x0 x1).
Definition term11 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term18 := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, (treal_le y1 y2) \/ (treal_le y2 y1)) y0.
Definition term9 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0)).
Definition term49 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_le (@pair hreal hreal x1 x2) (@pair hreal hreal x0 y0)) \/ (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x1 x2)).
Definition term56 := fun y0 : hreal => True.
Definition term44 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y0) \/ (treal_le y0 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 x3).
Definition term30 (x0 : hreal) := fun y0 : hreal => forall y1 : prod hreal hreal, (treal_le (@pair hreal hreal x0 y0) y1) \/ (treal_le y1 (@pair hreal hreal x0 y0)).
Definition term46 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y1) \/ (treal_le y1 (@pair hreal hreal x0 x1))) (@pair hreal hreal x2 y0).
Definition term41 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => (treal_le (@pair hreal hreal x0 x1) y1) \/ (treal_le y1 (@pair hreal hreal x0 x1))) y0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term4 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_le (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = (hreal_le (hreal_add y0 y1) (hreal_add y2 y3))) x0.
