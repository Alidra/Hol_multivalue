Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') := forall y0 : a0 -> Prop, (@CHOICE a0 y0) = (@ε a0 (fun y1 : a0 => @IN a0 y1 y0)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@CHOICE a0 y0) = (@ε a0 (fun y1 : a0 => @IN a0 y1 y0))) x0.
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => @ε a0 (fun y1 : a0 => @IN a0 y1 y0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => @ε a0 (fun y1 : a0 => @IN a0 y1 y0)) x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := @ε a0 (fun y0 : a0 => @IN a0 y0 x0).
