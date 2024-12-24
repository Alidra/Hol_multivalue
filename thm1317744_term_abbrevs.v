Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nadd -> Prop) := dest_hreal (mk_hreal x0).
Definition term4 (x0 : nadd -> Prop) := @eq Prop (exists y0 : nadd, x0 = (nadd_eq y0)).
Definition term2 (x0 : nadd -> Prop) := exists y0 : nadd, x0 = (nadd_eq y0).
Definition term0 (x0 : nadd -> Prop) := (fun y0 : nadd -> Prop => exists y1 : nadd, y0 = (nadd_eq y1)) x0.
Definition term3 (x0 : nadd -> Prop) := @eq Prop ((fun y0 : nadd -> Prop => exists y1 : nadd, y0 = (nadd_eq y1)) x0).
