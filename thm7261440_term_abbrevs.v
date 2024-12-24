Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y0 y3) = (y1 y3)) -> (@sum a0 y2 (fun y3 : a0 => y0 y3)) = (@sum a0 y2 y1).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (x2 y0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => x1 y0).
Definition term2 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@sum a0 x1 (fun y0 : a0 => x0 y0)) = (@sum a0 x1 x2).
Definition term4 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (x0 y2) = (y0 y2)) -> (@sum a0 y1 (fun y2 : a0 => x0 y2)) = (@sum a0 y1 y0).
Definition term3 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (x1 y1)) -> (@sum a0 y0 (fun y1 : a0 => x0 y1)) = (@sum a0 y0 x1).
