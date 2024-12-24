Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε (ind -> ind) (fun y0 : ind -> ind => exists y1 : ind, (forall y2 : ind, forall y3 : ind, ((y0 y2) = (y0 y3)) = (y2 = y3)) /\ (forall y2 : ind, ~ ((y0 y2) = y1))).
