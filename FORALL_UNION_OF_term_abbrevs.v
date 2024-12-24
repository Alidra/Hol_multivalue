Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : type686 a0) := forall y0 : a0 -> Prop, (@UNION_OF a0 x0 x1 y0) -> x2 y0.
Definition term1 (a0 : Type') (x0 : type180 a0) (x1 : type686 a0) (x2 : type686 a0) := forall y0 : type686 a0, ((x0 y0) /\ (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> x1 y1)) -> x2 (@UNIONS a0 y0).
