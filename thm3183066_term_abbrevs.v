Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@SETSPEC a0 x1 x0 y0) = (x0 /\ (x1 = y0))) x2.
Definition term1 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := x0 /\ (x1 = x2).
