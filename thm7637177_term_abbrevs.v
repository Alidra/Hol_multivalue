Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : nat) := ((forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@HAS_SIZE a0 x1 x2)) -> @HAS_SIZE a1 (@IMAGE a0 a1 x0 x1) x2.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : nat) := (fun y0 : nat => ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 x1) /\ ((@IN a0 y2 x1) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) /\ (@HAS_SIZE a0 x1 y0)) -> @HAS_SIZE a1 (@IMAGE a0 a1 x0 x1) y0) x2.
