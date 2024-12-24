Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : nat, forall y1 : list a0, (@EL a0 (S y0) y1) = (@EL a0 y0 (@tl a0 y1)).
