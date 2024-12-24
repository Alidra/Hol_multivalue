Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (x0 : hreal) := forall y0 : hreal, (treal_neg (@pair hreal hreal y0 x0)) = (@pair hreal hreal x0 y0).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term26 (x0 : hreal) (x1 : hreal) := @eq (prod hreal hreal) ((fun y0 : hreal => @pair hreal hreal y0 x0) x1).
Definition term21 (x0 : hreal) := @eq (hreal -> prod hreal hreal) ((fun y0 : hreal => fun y1 : hreal => @pair hreal hreal y1 y0) x0).
Definition term6 (x0 : hreal) (x1 : hreal) := @pair hreal hreal (@snd hreal hreal (@pair hreal hreal x0 x1)) (@fst hreal hreal (@pair hreal hreal x0 x1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@snd a0 a1 (@pair a0 a1 y0 y1)) = y1) x0.
Definition term17 := fun y0 : hreal => fun y1 : hreal => @pair hreal hreal y1 y0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0.
Definition term23 (x0 : hreal) := @eq (hreal -> prod hreal hreal) (fun y0 : hreal => @pair hreal hreal y0 x0).
Definition term0 := fun y0 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal y0) (@fst hreal hreal y0).
Definition term3 := forall y0 : prod hreal hreal, (treal_neg y0) = (@pair hreal hreal (@snd hreal hreal y0) (@fst hreal hreal y0)).
Definition term2 (x0 : prod hreal hreal) := @pair hreal hreal (@snd hreal hreal x0) (@fst hreal hreal x0).
Definition term18 (x0 : hreal) := (fun y0 : hreal => fun y1 : hreal => @pair hreal hreal y1 y0) x0.
Definition term24 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => @pair hreal hreal y0 x0) x1.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@fst a0 a1 (@pair a0 a1 y0 y1)) = y0) x0.
Definition term29 := forall y0 : hreal, forall y1 : hreal, (treal_neg (@pair hreal hreal y1 y0)) = (@pair hreal hreal y0 y1).
Definition term5 (x0 : hreal) (x1 : hreal) := treal_neg (@pair hreal hreal x0 x1).
Definition term19 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => fun y1 : hreal => @pair hreal hreal y1 y0) (@fst hreal hreal (@pair hreal hreal x0 x1)).
Definition term22 (x0 : hreal) := fun y0 : hreal => @pair hreal hreal y0 x0.
Definition term25 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => @pair hreal hreal y0 (@fst hreal hreal (@pair hreal hreal x0 x1))) (@snd hreal hreal (@pair hreal hreal x0 x1)).
Definition term20 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => @pair hreal hreal y0 (@fst hreal hreal (@pair hreal hreal x0 x1)).
Definition term1 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal y0) (@fst hreal hreal y0)) x0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0.
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0) x1.
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0) x1.
Definition term4 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_neg y0) = (@pair hreal hreal (@snd hreal hreal y0) (@fst hreal hreal y0))) x0.
Definition term27 (x0 : hreal) (x1 : hreal) := @eq (prod hreal hreal) (@pair hreal hreal x0 x1).
Definition term16 (x0 : hreal) (x1 : hreal) := @snd hreal hreal (@pair hreal hreal x0 x1).
Definition term15 (x0 : hreal) (x1 : hreal) := @fst hreal hreal (@pair hreal hreal x0 x1).
