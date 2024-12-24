Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (fun y0 : a1 => ((@pair a0 a1 x0 x2) = (@pair a0 a1 x1 y0)) = ((x0 = x1) /\ (x2 = y0))) x3.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (x0 = x1) /\ (x2 = x3).
