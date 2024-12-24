Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a1) := (fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0)) (@pair a0 a1 x1 x2).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := forall y0 : a1, (fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) (@pair a0 a1 x1 y0).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, (fun y2 : prod a0 a1 => x0 (@fst a0 a1 y2) (@snd a0 a1 y2)) (@pair a0 a1 y0 y1).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := fun y0 : a1 => x0 x1 y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) := forall y0 : prod a0 a1, x0 y0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := forall y0 : a1, x0 (@fst a0 a1 (@pair a0 a1 x1 y0)) (@snd a0 a1 (@pair a0 a1 x1 y0)).
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq Prop (forall y0 : prod a0 a1, x0 (@fst a0 a1 y0) (@snd a0 a1 y0)).
Definition term39 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : type1413 a0 a1, x0.
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, x0 y0 y1.
Definition term12 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq Prop (forall y0 : prod a0 a1, (fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) y0).
Definition term36 (a0 : Type') (a1 : Type') := forall y0 : type1413 a0 a1, (forall y1 : a0, forall y2 : a1, y0 y1 y2) = (forall y1 : prod a0 a1, y0 (@fst a0 a1 y1) (@snd a0 a1 y1)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a1) := x0 (@fst a0 a1 (@pair a0 a1 x1 x2)).
Definition term33 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq Prop (((forall y0 : a0, forall y1 : a1, x0 y0 y1) = (forall y0 : a0, forall y1 : a1, x0 y0 y1)) = True).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0).
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a1) := x0 (@fst a0 a1 (@pair a0 a1 x1 x2)) (@snd a0 a1 (@pair a0 a1 x1 x2)).
Definition term32 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq Prop ((fun y0 : Prop => y0 = True) ((forall y0 : a0, forall y1 : a1, x0 y0 y1) = (forall y0 : a0, forall y1 : a1, x0 y0 y1))).
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := fun y0 : a1 => (fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) (@pair a0 a1 x1 y0).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := forall y0 : a1, x0 x1 y0.
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : prod a0 a1, (fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) y0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) := forall y0 : a0, forall y1 : a1, x0 (@pair a0 a1 y0 y1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq Prop (forall y0 : a0, forall y1 : a1, x0 y0 y1).
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, x0 (@fst a0 a1 (@pair a0 a1 y0 y1)) (@snd a0 a1 (@pair a0 a1 y0 y1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : prod a0 a1, x0 (@fst a0 a1 y0) (@snd a0 a1 y0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : prod a0 a1 => (fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) y0.
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : prod a0 a1) := (fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0)) x1.
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := fun y0 : a1 => x0 (@fst a0 a1 (@pair a0 a1 x1 y0)) (@snd a0 a1 (@pair a0 a1 x1 y0)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : Prop => y0 = True) ((forall y0 : a0, forall y1 : a1, x0 y0 y1) = (forall y0 : a0, forall y1 : a1, x0 y0 y1)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : a0 => forall y1 : a1, x0 y0 y1.
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : a0 => forall y1 : a1, (fun y2 : prod a0 a1 => x0 (@fst a0 a1 y2) (@snd a0 a1 y2)) (@pair a0 a1 y0 y1).
Definition term35 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => True.
Definition term34 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => (forall y1 : a0, forall y2 : a1, y0 y1 y2) = (forall y1 : prod a0 a1, y0 (@fst a0 a1 y1) (@snd a0 a1 y1)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := fun y0 : a0 => forall y1 : a1, x0 (@fst a0 a1 (@pair a0 a1 y0 y1)) (@snd a0 a1 (@pair a0 a1 y0 y1)).
Definition term37 (a0 : Type') (a1 : Type') := forall y0 : type1413 a0 a1, True.
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : prod a0 a1) := x0 (@fst a0 a1 x1) (@snd a0 a1 x1).
