Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : type919 a0) (x1 : a0) := x0 (fun y0 : Prop => fun y1 : a0 => y0 /\ (x1 = y1)).
Definition term0 (a0 : Type') (x0 : a0) := fun y0 : Prop => fun y1 : a0 => y0 /\ (x0 = y1).
Definition term1 (a0 : Type') (x0 : type919 a0) (x1 : a0) := x0 (@SETSPEC a0 x1).