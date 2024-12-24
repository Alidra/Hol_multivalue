Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := (fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0)) (@pair a0 a1 x1 x2).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term21 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) := fun y0 : a1 => ((fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) (@pair a0 a1 x1 y0)) = (x0 x1 y0).
Definition term25 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term23 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) := forall y0 : a1, ((fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) (@pair a0 a1 x1 y0)) = (x0 x1 y0).
Definition term24 (a0 : Type') := forall y0 : a0, True.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@snd a0 a1 (@pair a0 a1 y0 y1)) = y1) x0.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0.
Definition term28 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := exists y0 : type1209 a0 a1 a2, forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = (x0 y1 y2).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@fst a0 a1 (@pair a0 a1 y0 y1)) = y0) x0.
Definition term19 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := x0 (@fst a0 a1 (@pair a0 a1 x1 x2)).
Definition term10 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := (fun y0 : prod a0 a1 => (fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) y0) (@pair a0 a1 x1 x2).
Definition term12 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0).
Definition term18 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := x0 (@fst a0 a1 (@pair a0 a1 x1 x2)) (@snd a0 a1 (@pair a0 a1 x1 x2)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term22 (a0 : Type') := fun y0 : a0 => True.
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1209 a0 a1 a2) (x1 : prod a0 a1) := (fun y0 : prod a0 a1 => x0 y0) x1.
Definition term20 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := @eq a2 (x0 x1 x2).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0.
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := @eq a2 ((fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0)) (@pair a0 a1 x1 x2)).
Definition term30 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type1412 a0 a1 a2, exists y1 : type1209 a0 a1 a2, forall y2 : a0, forall y3 : a1, (y1 (@pair a0 a1 y2 y3)) = (y0 y2 y3).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0) x1.
Definition term27 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := forall y0 : a0, forall y1 : a1, ((fun y2 : prod a0 a1 => x0 (@fst a0 a1 y2) (@snd a0 a1 y2)) (@pair a0 a1 y0 y1)) = (x0 y0 y1).
Definition term16 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : a0) (x2 : a1) := @eq a2 ((fun y0 : prod a0 a1 => (fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) y0) (@pair a0 a1 x1 x2)).
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := fun y0 : prod a0 a1 => (fun y1 : prod a0 a1 => x0 (@fst a0 a1 y1) (@snd a0 a1 y1)) y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0) x1.
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : prod a0 a1) := (fun y0 : prod a0 a1 => x0 (@fst a0 a1 y0) (@snd a0 a1 y0)) x1.
Definition term26 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := fun y0 : a0 => forall y1 : a1, ((fun y2 : prod a0 a1 => x0 (@fst a0 a1 y2) (@snd a0 a1 y2)) (@pair a0 a1 y0 y1)) = (x0 y0 y1).
Definition term29 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) := fun y0 : type1209 a0 a1 a2 => forall y1 : a0, forall y2 : a1, (y0 (@pair a0 a1 y1 y2)) = (x0 y1 y2).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1412 a0 a1 a2) (x1 : prod a0 a1) := x0 (@fst a0 a1 x1) (@snd a0 a1 x1).
