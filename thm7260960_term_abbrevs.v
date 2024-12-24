Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@sum a0 x1 x0) = (@sum a0 x1 x2).
Definition term0 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (fun y0 : a0 -> real => (forall y1 : a0, (@IN a0 y1 x1) -> (x0 y1) = (y0 y1)) -> (@sum a0 x1 x0) = (@sum a0 x1 y0)) x2.
