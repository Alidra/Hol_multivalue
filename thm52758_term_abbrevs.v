Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type1228 a0 a1 a2, (@GABS ((prod a2 a1) -> a0) (fun y1 : type1228 a0 a1 a2 => forall y2 : a2, forall y3 : a1, @GEQ a0 (y1 (@pair a2 a1 y2 y3)) (y0 (@pair a2 a1 y2 y3)))) = y0.
