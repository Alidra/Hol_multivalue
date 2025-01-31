Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0) (x1 : type919 a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => x1 (@SETSPEC a0 y0))).
Definition term2 (a0 : Type') (x0 : type919 a0) (x1 : a0) := x0 (fun y0 : Prop => fun y1 : a0 => y0 /\ (x1 = y1)).
Definition term0 (a0 : Type') (x0 : type919 a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => x0 (@SETSPEC a0 y1)))) = (x0 (fun y1 : Prop => fun y2 : a0 => y1 /\ (y0 = y2)))) x1.
