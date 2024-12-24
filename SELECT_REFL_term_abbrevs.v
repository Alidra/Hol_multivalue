Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (a0 : Type') := forall y0 : a0, (@ε a0 (fun y1 : a0 => y1 = y0)) = y0.
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => y0 = x0) (@ε a0 (fun y0 : a0 => y0 = x0)).
Definition term5 (a0 : Type') (x0 : a0) := @eq Prop ((fun y0 : a0 => y0 = x0) (@ε a0 (fun y0 : a0 => y0 = x0))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := x0 (@ε a0 x0).
Definition term2 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term3 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term6 (a0 : Type') (x0 : a0) := @eq Prop ((@ε a0 (fun y0 : a0 => y0 = x0)) = x0).
Definition term4 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => y0 = x0).
