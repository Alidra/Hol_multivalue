Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@EL a0 (NUMERAL 0) y0) = (@hd a0 y0)) x0.
Definition term0 (a0 : Type') := forall y0 : list a0, (@EL a0 (NUMERAL 0) y0) = (@hd a0 y0).
