Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1) x0.
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := exists y0 : a0, (x0 = y0) /\ (x1 = x2).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => forall y1 : a0, forall y2 : a1, ((@pair a0 a1 x0 y0) = (@pair a0 a1 y1 y2)) = ((x0 = y1) /\ (y0 = y2))) x1.
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @ε a1 (fun y0 : a1 => exists y1 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y1 y0)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @ε a1 (fun y0 : a1 => exists y1 : a0, x0 = (@pair a0 a1 y1 y0)).
Definition term35 (a0 : Type') (x0 : a0) := exists y0 : a0, x0 = y0.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, forall y2 : a0, forall y3 : a1, ((@pair a0 a1 y0 y1) = (@pair a0 a1 y2 y3)) = ((y0 = y2) /\ (y1 = y3))) x0.
Definition term15 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1) -> forall y0 : a0 -> Prop, forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1.
Definition term41 (a0 : Type') (a1 : Type') := forall y0 : a0, forall y1 : a1, (@snd a0 a1 (@pair a0 a1 y0 y1)) = y1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (fun y0 : a1 => ((@pair a0 a1 x0 x2) = (@pair a0 a1 x1 y0)) = ((x0 = x1) /\ (x2 = y0))) x3.
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := (exists y0 : a0, (x0 = y0) /\ (x2 = x1)) -> x1 = x2.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (x0 y0) = (y0 = x1).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := (x2 = x1) -> exists y0 : a0, (x0 = y0) /\ (x1 = x2).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) /\ True.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, (x0 y0) = (y0 = x1)) -> (@ε a0 x0) = x1.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := fun y0 : a0 => (x0 = y0) /\ (x1 = x2).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (forall y1 : a0, (x0 y1) = (y1 = y0)) -> (@ε a0 x0) = y0) x1.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := (fun y0 : a1 => exists y1 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y1 y0)) x2.
Definition term39 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : a1, ((fun y1 : a1 => exists y2 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y2 y1)) y0) = (y0 = x1).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (forall y1 : a0, (x0 y1) = (y1 = y0)) -> (@ε a0 x0) = y0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (x0 = x1) /\ (x2 = x3).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0.
Definition term38 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := ((exists y0 : a0, (x0 = y0) /\ (x1 = x2)) -> x2 = x1) /\ ((x2 = x1) -> exists y0 : a0, (x0 = y0) /\ (x1 = x2)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, forall y1 : a0, forall y2 : a1, ((@pair a0 a1 x0 y0) = (@pair a0 a1 y1 y2)) = ((x0 = y1) /\ (y0 = y2)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := exists y0 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y0 x2).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : a0, forall y1 : a1, ((@pair a0 a1 x0 x1) = (@pair a0 a1 y0 y1)) = ((x0 = y0) /\ (x1 = y1)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := fun y0 : a0 => (@pair a0 a1 x0 x1) = (@pair a0 a1 y0 x2).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0 -> Prop, forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1) -> (@ε a0 x0) = x1.
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (forall y0 : a1, ((fun y1 : a1 => exists y2 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y2 y1)) y0) = (y0 = x1)) -> (@ε a1 (fun y0 : a1 => exists y1 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y1 y0))) = x1.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq a1 (@snd a0 a1 (@pair a0 a1 x0 x1)).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := @eq Prop ((fun y0 : a1 => exists y1 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y1 y0)) x2).
Definition term16 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => (@snd a0 a1 y0) = (@ε a1 (fun y1 : a1 => exists y2 : a0, y0 = (@pair a0 a1 y2 y1)))) x0.
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq a1 (@ε a1 (fun y0 : a1 => exists y1 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y1 y0))).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := @eq Prop (exists y0 : a0, (x0 = y0) /\ (x1 = x2)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a1) := @eq Prop (exists y0 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y0 x2)).
Definition term34 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) := forall y0 : a1, ((@pair a0 a1 x0 x2) = (@pair a0 a1 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := fun y0 : a1 => exists y1 : a0, (@pair a0 a1 x0 x1) = (@pair a0 a1 y1 y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) := (fun y0 : a0 => forall y1 : a1, ((@pair a0 a1 x0 x1) = (@pair a0 a1 y0 y1)) = ((x0 = y0) /\ (x1 = y1))) x2.
Definition term8 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (forall y2 : a0, (y0 y2) = (y2 = y1)) -> (@ε a0 y0) = y1.
