Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : type1430 a0 a1 a2) := x0 (fun y0 : a0 => @pair a1 a2 (@fst a1 a2 (x1 y0)) (@snd a1 a2 (x1 y0))).
Definition term30 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : a0 -> a1) (x2 : a0 -> a2) := (fun y0 : a0 -> a2 => x0 (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1))) x2.
Definition term36 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := @pair a1 a2 ((fun y0 : a0 => @fst a1 a2 (x0 y0)) x1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term21 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : a0 -> a1) := fun y0 : a0 -> a2 => x0 (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1)).
Definition term26 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := @pair a1 a2 (@fst a1 a2 (x0 x1)) (@snd a1 a2 (x0 x1)).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : type1430 a0 a1 a2) := (fun y0 : type1430 a0 a1 a2 => x0 y0) x1.
Definition term16 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) := fun y0 : a0 => @pair a1 a2 (x0 y0) (x1 y0).
Definition term22 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, x0.
Definition term37 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := @pair a1 a2 (@fst a1 a2 (x0 x1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => y0 = (fun y1 : a0 => y0 y1)) x0.
Definition term33 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) := fun y0 : a0 => @snd a1 a2 (x0 y0).
Definition term25 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : type1430 a0 a1 a2) := x0 (fun y0 : a0 => x1 y0).
Definition term19 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : a0 -> a1) := forall y0 : a0 -> a2, x0 (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1)).
Definition term43 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : type1430 a0 a1 a2) := @eq Prop (x0 (fun y0 : a0 => @pair a1 a2 (@fst a1 a2 (x1 y0)) (@snd a1 a2 (x1 y0)))).
Definition term47 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type478 a0 a1 a2, (forall y1 : type1430 a0 a1 a2, y0 y1) = (forall y1 : a0 -> a1, forall y2 : a0 -> a2, y0 (fun y3 : a0 => @pair a1 a2 (y1 y3) (y2 y3))).
Definition term38 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := (fun y0 : a0 => @snd a1 a2 (x0 y0)) x1.
Definition term4 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, y0 = (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)).
Definition term2 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => y0 = (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)).
Definition term31 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : type1430 a0 a1 a2) := x0 (fun y0 : a0 => @pair a1 a2 ((fun y1 : a0 => @fst a1 a2 (x1 y1)) y0) ((fun y1 : a0 => @snd a1 a2 (x1 y1)) y0)).
Definition term23 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := fun y0 : a0 -> a1 => forall y1 : a0 -> a2, x0 (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2)).
Definition term27 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) := fun y0 : a0 => @pair a1 a2 (@fst a1 a2 (x0 y0)) (@snd a1 a2 (x0 y0)).
Definition term45 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := (forall y0 : type1430 a0 a1 a2, x0 y0) -> forall y0 : a0 -> a1, forall y1 : a0 -> a2, x0 (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2)).
Definition term10 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, y0 = (fun y1 : a0 => y0 y1).
Definition term29 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a2, x0 (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2))) x1.
Definition term35 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := @fst a1 a2 (x0 x1).
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := forall y0 : a0 -> a1, forall y1 : a0 -> a2, x0 (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2)).
Definition term18 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => True.
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0.
Definition term42 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : type1430 a0 a1 a2) := @eq Prop (x0 (fun y0 : a0 => @pair a1 a2 ((fun y1 : a0 => @fst a1 a2 (x1 y1)) y0) ((fun y1 : a0 => @snd a1 a2 (x1 y1)) y0))).
Definition term24 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) := fun y0 : a0 => x0 y0.
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) (x1 : a0 -> a1) (x2 : a0 -> a2) := x0 (fun y0 : a0 => @pair a1 a2 (x1 y0) (x2 y0)).
Definition term1 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0.
Definition term7 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0.
Definition term41 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) := fun y0 : a0 => @pair a1 a2 ((fun y1 : a0 => @fst a1 a2 (x0 y1)) y0) ((fun y1 : a0 => @snd a1 a2 (x0 y1)) y0).
Definition term8 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => y0 = (fun y1 : a0 => y0 y1).
Definition term5 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => y0 = (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0))) x0.
Definition term12 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := forall y0 : type1430 a0 a1 a2, x0 y0.
Definition term44 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := (forall y0 : a0 -> a1, forall y1 : a0 -> a2, x0 (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2))) -> forall y0 : type1430 a0 a1 a2, x0 y0.
Definition term32 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) := fun y0 : a0 => @fst a1 a2 (x0 y0).
Definition term39 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := @snd a1 a2 (x0 x1).
Definition term9 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, (fun y1 : a0 => y0 y1) = y0.
Definition term40 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := @pair a1 a2 ((fun y0 : a0 => @fst a1 a2 (x0 y0)) x1) ((fun y0 : a0 => @snd a1 a2 (x0 y0)) x1).
Definition term46 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := ((forall y0 : type1430 a0 a1 a2, x0 y0) -> forall y0 : a0 -> a1, forall y1 : a0 -> a2, x0 (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2))) /\ ((forall y0 : a0 -> a1, forall y1 : a0 -> a2, x0 (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2))) -> forall y0 : type1430 a0 a1 a2, x0 y0).
Definition term34 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := (fun y0 : a0 => @fst a1 a2 (x0 y0)) x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @pair a0 a1 (@fst a0 a1 x0) (@snd a0 a1 x0).
Definition term20 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, True.
