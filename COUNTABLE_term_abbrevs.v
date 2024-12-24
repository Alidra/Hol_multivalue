Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => @ge_c a0 nat (@UNIV nat) y0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => @ge_c a0 nat (@UNIV nat) y0) x0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@COUNTABLE a0 y0) = (@ge_c a0 nat (@UNIV nat) y0)) x0.
Definition term2 (a0 : Type') := forall y0 : a0 -> Prop, (@COUNTABLE a0 y0) = (@ge_c a0 nat (@UNIV nat) y0).
