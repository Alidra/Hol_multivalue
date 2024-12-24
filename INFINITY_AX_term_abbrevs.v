Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := exists y0 : ind -> ind, (@ONE_ONE ind ind y0) /\ (~ (@ONTO ind ind y0)).
