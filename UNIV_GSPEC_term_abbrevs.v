Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 True y1).
