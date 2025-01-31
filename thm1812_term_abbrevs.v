Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => (exists y1 : a0, y0) = y0) x0.
