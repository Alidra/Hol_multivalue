Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := x0 (@pair a2 a1 x1 x2).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : prod a2 a1) := (fun y0 : prod a2 a1 => x0 y0) x1.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := (fun y0 : prod a2 a1 => x0 y0) (@pair a2 a1 x1 x2).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := @eq a0 (x0 (@pair a2 a1 x1 x2)).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1228 a0 a1 a2) (x1 : a2) (x2 : a1) := @eq a0 ((fun y0 : prod a2 a1 => x0 y0) (@pair a2 a1 x1 x2)).
