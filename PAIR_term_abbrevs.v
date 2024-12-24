Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @pair a0 a1 (@fst a0 a1 (@pair a0 a1 x0 x1)) (@snd a0 a1 (@pair a0 a1 x0 x1)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @eq Prop ((fun y0 : prod a0 a1 => (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0) x0).
Definition term9 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := exists y0 : a0, exists y1 : a1, x0 = (@pair a0 a1 y0 y1).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@snd a0 a1 (@pair a0 a1 y0 y1)) = y1) x0.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0.
Definition term21 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := fun y0 : a1 => x0 = (@pair a0 a1 x1 y0).
Definition term8 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@pair a0 a1 y1 y2)) x0.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq (prod a0 a1) (@pair a0 a1 x0 x1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@fst a0 a1 (@pair a0 a1 y0 y1)) = y0) x0.
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq (prod a0 a1) (@pair a0 a1 (@fst a0 a1 (@pair a0 a1 x0 x1)) (@snd a0 a1 (@pair a0 a1 x0 x1))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := exists y0 : a1, x0 = (@pair a0 a1 x1 y0).
Definition term22 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := fun y0 : a0 => exists y1 : a1, x0 = (@pair a0 a1 y0 y1).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @pair a0 a1 (@fst a0 a1 (@pair a0 a1 x0 x1)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : prod a0 a1 => (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0) (@pair a0 a1 x0 x1).
Definition term17 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @eq Prop ((@pair a0 a1 (@fst a0 a1 x0) (@snd a0 a1 x0)) = x0).
Definition term23 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0) x0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0) x1.
Definition term11 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0) x1.
Definition term16 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @pair a0 a1 (@fst a0 a1 x0) (@snd a0 a1 x0).
