Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) -> y0 (@ε a0 y0).