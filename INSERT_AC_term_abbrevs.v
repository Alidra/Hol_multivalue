Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@INSERT a0 x0 (@INSERT a0 y0 y1)) = (@INSERT a0 y0 (@INSERT a0 x0 y1))) x1.
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @INSERT a0 x0 (@INSERT a0 x1 x2).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := and ((@INSERT a0 x1 (@INSERT a0 x0 x2)) = (@INSERT a0 x0 (@INSERT a0 x1 x2))).
Definition term4 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@INSERT a0 y0 (@INSERT a0 y1 y2)) = (@INSERT a0 y1 (@INSERT a0 y0 y2))) x0.
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@INSERT a0 x1 (@INSERT a0 x0 y0)) = (@INSERT a0 x0 (@INSERT a0 x1 y0)).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := ((@INSERT a0 x1 (@INSERT a0 x0 x2)) = (@INSERT a0 x0 (@INSERT a0 x1 x2))) /\ ((@INSERT a0 x1 (@INSERT a0 x1 x2)) = (@INSERT a0 x1 x2)).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @INSERT a0 x0 (@INSERT a0 x0 x1).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@INSERT a0 x0 (@INSERT a0 x0 y0)) = (@INSERT a0 x0 y0).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @eq (a0 -> Prop) (@INSERT a0 x0 (@INSERT a0 x1 x2)).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@INSERT a0 y0 (@INSERT a0 y0 y1)) = (@INSERT a0 y0 y1)) x0.
Definition term5 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@INSERT a0 x0 (@INSERT a0 y0 y1)) = (@INSERT a0 y0 (@INSERT a0 x0 y1)).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq (a0 -> Prop) (@INSERT a0 x0 x1).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq (a0 -> Prop) (@INSERT a0 x0 (@INSERT a0 x0 x1)).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@INSERT a0 x0 (@INSERT a0 x0 y0)) = (@INSERT a0 x0 y0)) x1.
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@INSERT a0 x1 (@INSERT a0 x0 y0)) = (@INSERT a0 x0 (@INSERT a0 x1 y0))) x2.
