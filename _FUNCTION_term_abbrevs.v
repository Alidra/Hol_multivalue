Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : type1413 a0 a1 => fun y1 : a0 => @COND a1 (@ex1 a1 (y0 y1)) (@ε a1 (y0 y1)) (@ε a1 (fun y2 : a1 => False)).
