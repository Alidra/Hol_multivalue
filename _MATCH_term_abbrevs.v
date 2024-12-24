Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a0 => fun y1 : type1413 a0 a1 => @COND a1 (@ex1 a1 (y1 y0)) (@ε a1 (y1 y0)) (@ε a1 (fun y2 : a1 => False)).
