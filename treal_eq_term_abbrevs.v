Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term37 (x0 : hreal) (x1 : hreal) (x2 : hreal) := @eq (hreal -> Prop) ((fun y0 : hreal => fun y1 : hreal => (hreal_add x0 y1) = (hreal_add y0 x1)) x2).
Definition term6 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_eq y0 y1) = ((hreal_add (@fst hreal hreal y0) (@snd hreal hreal y1)) = (hreal_add (@fst hreal hreal y1) (@snd hreal hreal y0))).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term8 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_eq x0 y0) = ((hreal_add (@fst hreal hreal x0) (@snd hreal hreal y0)) = (hreal_add (@fst hreal hreal y0) (@snd hreal hreal x0)))) x1.
Definition term3 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (hreal_add (@fst hreal hreal x0) (@snd hreal hreal y0)) = (hreal_add (@fst hreal hreal y0) (@snd hreal hreal x0))) x1.
Definition term43 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq Prop ((hreal_add x0 x1) = (hreal_add x2 x3)).
Definition term30 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => fun y1 : hreal => (hreal_add (@fst hreal hreal (@pair hreal hreal x0 x1)) y1) = (hreal_add y0 (@snd hreal hreal (@pair hreal hreal x0 x1))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@snd a0 a1 (@pair a0 a1 y0 y1)) = y1) x0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0.
Definition term36 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := fun y0 : hreal => (hreal_add (@fst hreal hreal (@pair hreal hreal x2 x3)) y0) = (hreal_add (@fst hreal hreal (@pair hreal hreal x0 x1)) (@snd hreal hreal (@pair hreal hreal x2 x3))).
Definition term2 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (hreal_add (@fst hreal hreal x0) (@snd hreal hreal y0)) = (hreal_add (@fst hreal hreal y0) (@snd hreal hreal x0)).
Definition term23 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => fun y3 : hreal => (hreal_add y0 y3) = (hreal_add y2 y1)) (@fst hreal hreal (@pair hreal hreal x0 x1)).
Definition term26 (x0 : hreal) := fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => (hreal_add x0 y2) = (hreal_add y1 y0).
Definition term24 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => (hreal_add (@fst hreal hreal (@pair hreal hreal x0 x1)) y2) = (hreal_add y1 y0).
Definition term28 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => (hreal_add x0 y2) = (hreal_add y1 y0)) x1.
Definition term33 (x0 : hreal) (x1 : hreal) := @eq (hreal -> hreal -> Prop) (fun y0 : hreal => fun y1 : hreal => (hreal_add x0 y1) = (hreal_add y0 x1)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@fst a0 a1 (@pair a0 a1 y0 y1)) = y0) x0.
Definition term42 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq Prop ((fun y0 : hreal => (hreal_add x0 y0) = (hreal_add x1 x2)) x3).
Definition term47 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_eq (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = ((hreal_add y0 y1) = (hreal_add y2 y3)).
Definition term46 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2)).
Definition term45 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1)).
Definition term4 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := hreal_add (@fst hreal hreal x0) (@snd hreal hreal x1).
Definition term5 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_eq x0 y0) = ((hreal_add (@fst hreal hreal x0) (@snd hreal hreal y0)) = (hreal_add (@fst hreal hreal y0) (@snd hreal hreal x0))).
Definition term34 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => fun y1 : hreal => (hreal_add x0 y1) = (hreal_add y0 x1)) x2.
Definition term35 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => fun y1 : hreal => (hreal_add (@fst hreal hreal (@pair hreal hreal x0 x1)) y1) = (hreal_add y0 (@snd hreal hreal (@pair hreal hreal x0 x1)))) (@fst hreal hreal (@pair hreal hreal x2 x3)).
Definition term29 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => (hreal_add (@fst hreal hreal (@pair hreal hreal x0 x1)) y2) = (hreal_add y1 y0)) (@snd hreal hreal (@pair hreal hreal x0 x1)).
Definition term1 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => fun y1 : prod hreal hreal => (hreal_add (@fst hreal hreal y0) (@snd hreal hreal y1)) = (hreal_add (@fst hreal hreal y1) (@snd hreal hreal y0))) x0.
Definition term38 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (hreal_add x0 y0) = (hreal_add x1 x2).
Definition term7 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_eq y0 y1) = ((hreal_add (@fst hreal hreal y0) (@snd hreal hreal y1)) = (hreal_add (@fst hreal hreal y1) (@snd hreal hreal y0)))) x0.
Definition term39 (x0 : hreal) (x1 : hreal) (x2 : hreal) := @eq (hreal -> Prop) (fun y0 : hreal => (hreal_add x0 y0) = (hreal_add x1 x2)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0) x1.
Definition term40 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (hreal_add x0 y0) = (hreal_add x1 x2)) x3.
Definition term22 (x0 : hreal) := (fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => fun y3 : hreal => (hreal_add y0 y3) = (hreal_add y2 y1)) x0.
Definition term44 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0) x1.
Definition term25 (x0 : hreal) := @eq (hreal -> hreal -> hreal -> Prop) ((fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => fun y3 : hreal => (hreal_add y0 y3) = (hreal_add y2 y1)) x0).
Definition term31 (x0 : hreal) (x1 : hreal) := @eq (hreal -> hreal -> Prop) ((fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => (hreal_add x0 y2) = (hreal_add y1 y0)) x1).
Definition term10 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (@fst hreal hreal (@pair hreal hreal x0 x1)) (@snd hreal hreal (@pair hreal hreal x2 x3)).
Definition term0 := fun y0 : prod hreal hreal => fun y1 : prod hreal hreal => (hreal_add (@fst hreal hreal y0) (@snd hreal hreal y1)) = (hreal_add (@fst hreal hreal y1) (@snd hreal hreal y0)).
Definition term9 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term27 (x0 : hreal) := @eq (hreal -> hreal -> hreal -> Prop) (fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => (hreal_add x0 y2) = (hreal_add y1 y0)).
Definition term21 := fun y0 : hreal => fun y1 : hreal => fun y2 : hreal => fun y3 : hreal => (hreal_add y0 y3) = (hreal_add y2 y1).
Definition term20 (x0 : hreal) (x1 : hreal) := @snd hreal hreal (@pair hreal hreal x0 x1).
Definition term32 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => fun y1 : hreal => (hreal_add x0 y1) = (hreal_add y0 x1).
Definition term41 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (hreal_add (@fst hreal hreal (@pair hreal hreal x0 x1)) y0) = (hreal_add (@fst hreal hreal (@pair hreal hreal x2 x3)) (@snd hreal hreal (@pair hreal hreal x0 x1)))) (@snd hreal hreal (@pair hreal hreal x2 x3)).
Definition term19 (x0 : hreal) (x1 : hreal) := @fst hreal hreal (@pair hreal hreal x0 x1).
