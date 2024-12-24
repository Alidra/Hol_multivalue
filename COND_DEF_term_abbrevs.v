Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : Prop => fun y1 : a0 => fun y2 : a0 => @ε a0 (fun y3 : a0 => ((y0 = True) -> y3 = y1) /\ ((y0 = False) -> y3 = y2)).
