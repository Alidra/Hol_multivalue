Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := forall y0 : a1, (x0 y0) -> forall y1 : a0, x1 y0 y1.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := forall y0 : a0, forall y1 : a1, (x0 y1) -> x1 y1 y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := (~ ((forall y0 : a1, (x0 y0) -> forall y1 : a0, x1 y0 y1) = (forall y0 : a0, forall y1 : a1, (x0 y1) -> x1 y1 y0))) -> False.
