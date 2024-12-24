Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := exists y0 : Prop, y0.
Definition term2 := fun y0 : Prop => y0.
Definition term5 := (fun y0 : Prop => y0) (@ε Prop (fun y0 : Prop => y0)).
Definition term1 := fun y0 : Prop -> Prop => y0 (@ε Prop y0).
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term4 := (fun y0 : Prop -> Prop => y0 (@ε Prop y0)) (fun y0 : Prop => y0).
