Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (x2 y0).