Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
