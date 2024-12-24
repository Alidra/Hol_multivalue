Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := x0 (@pair a1 a0 x1 x2).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => x0 (@pair a1 a0 x1 y0)) x2.
Definition term4 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, y0 = (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)).
Definition term2 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => y0 = (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := (fun y0 : a1 => forall y1 : a0, x0 (@pair a1 a0 y0 y1)) x1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0.
Definition term1 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0)) = y0.
Definition term5 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => y0 = (@pair a0 a1 (@fst a0 a1 y0) (@snd a0 a1 y0))) x0.
Definition term15 (a0 : Type') (a1 : Type') := forall y0 : type1223 a0 a1, (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2)) -> forall y1 : prod a1 a0, y0 y1.
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1)) -> forall y0 : prod a1 a0, x0 y0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := @pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0).
Definition term0 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @pair a0 a1 (@fst a0 a1 x0) (@snd a0 a1 x0).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := x0 (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1)).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := forall y0 : a0, x0 (@pair a1 a0 x1 y0).
