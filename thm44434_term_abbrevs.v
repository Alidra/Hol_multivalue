Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @REP_prod a0 a1 (@ABS_prod a0 a1 x0).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0, exists y1 : a1, x0 = (@mk_pair a0 a1 y0 y1).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)) x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq Prop (exists y0 : a0, exists y1 : a1, x0 = (@mk_pair a0 a1 y0 y1)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := @eq Prop ((fun y0 : type1413 a0 a1 => exists y1 : a0, exists y2 : a1, y0 = (@mk_pair a0 a1 y1 y2)) x0).
