Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @ε a1 (fun y0 : a1 => exists y1 : a0, x0 = (@pair a0 a1 y1 y0)).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => @ε a1 (fun y1 : a1 => exists y2 : a0, y0 = (@pair a0 a1 y2 y1)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => @ε a1 (fun y1 : a1 => exists y2 : a0, y0 = (@pair a0 a1 y2 y1))) x0.
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, (@snd a0 a1 y0) = (@ε a1 (fun y1 : a1 => exists y2 : a0, y0 = (@pair a0 a1 y2 y1))).
