Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) = ((y0 = (@EMPTY a0)) \/ (exists y1 : a0, exists y2 : a0 -> Prop, (y0 = (@INSERT a0 y1 y2)) /\ (@FINITE a0 y2))).
