Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) := ((forall y0 : a0, (@IN a0 y0 x2) -> exists y1 : a1, (x0 y1) = y0) /\ (forall y0 : a1, (@IN a0 (x0 y0) x2) = (@IN a1 y0 x1))) -> (@IMAGE a1 a0 x0 x1) = x2.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, (@IN a0 y1 y0) -> exists y2 : a1, (x0 y2) = y1) /\ (forall y1 : a1, (@IN a0 (x0 y1) y0) = (@IN a1 y1 x1))) -> (@IMAGE a1 a0 x0 x1) = y0) x2.
