Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @ε a0 (fun y0 : a0 => exists y1 : a1, x0 = (@pair a0 a1 y0 y1)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => @ε a0 (fun y1 : a0 => exists y2 : a1, y0 = (@pair a0 a1 y1 y2))) x0.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => @ε a0 (fun y1 : a0 => exists y2 : a1, y0 = (@pair a0 a1 y1 y2)).
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, (@fst a0 a1 y0) = (@ε a0 (fun y1 : a0 => exists y2 : a1, y0 = (@pair a0 a1 y1 y2))).
